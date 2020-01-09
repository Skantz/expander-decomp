// Authored by Ludvig Janiuk 2019 as part of individual project at KTH.
#pragma clang diagnostic push
#pragma ide diagnostic ignored "cert-msc32-c"
#pragma ide diagnostic ignored "cppcoreguidelines-slicing"

#include <iostream>
#include <algorithm>
#include <random>
#include <memory>
#include <vector>
#include <array>
#include <set>
#include <chrono>
#include <cstdlib>
#include <bits/stdc++.h>
#include <lemon/core.h>
#include <lemon/connectivity.h>
#include <lemon/adaptors.h>
#include <lemon/list_graph.h>
#include <lemon/edge_set.h>
#include <lemon/preflow.h>

#include "cxxopts.hpp"
#include "preliminaries.h"

#include<lemon/graph_to_eps.h>
#include <lemon/lgf_writer.h>

// TODO now
// Clean the code much more, to be able to do the stopping and edge version
// Basically get unnecessary stuff out of the algo

using namespace lemon;
using namespace std;
using namespace std::chrono;

using G = ListGraph;
using NodeMapd = typename G::template NodeMap<double>;
using Node = typename G::Node;
using NodeIt = typename G::NodeIt;
using Snapshot = typename G::Snapshot;
using Edge = typename G::Edge;
using EdgeIt = typename G::EdgeIt;
using IncEdgeIt = typename G::IncEdgeIt;
using OutArcIt = typename G::OutArcIt;
using Paths = vector<array<Node, 2>>;
using ArcLookup = ArcLookUp<G>;
// LEMON uses ints internally. We might want to look into this
template<class T>
using EdgeMap = typename G::template EdgeMap<T>;
using EdgeMapi = EdgeMap<int>;
template<class T>
using NodeMap = typename G::template NodeMap<T>;
using NodeMapi = NodeMap<int>;
using NodeNeighborMap = NodeMap<vector<tuple<Node, int>>>;
using FlowAlgo = Preflow<G, EdgeMapi>;
using Matching = ListEdgeSet<ListGraph>;
using Matchingp = unique_ptr<Matching>;
using Bisection = set<Node>;
using Bisectionp = unique_ptr<Bisection>;
using Cut = set<Node>;
using Cutp = unique_ptr<Cut>;
using CutMap = NodeMap<bool>;


// TO categorize a little, what are the run options...
// Tbh these should maybe be separeate programs...

// Either we generatea graph or load it from file
// So basically, "what's the source of the graph", there needs to be a graph and it has to come from somewhere...

// Then, what do we do with the graph, we run the cutmatching game on it right, what parameters

// Finally, what do we do with the output

// TODO Purge basically
// PARAMETERS:
bool PRINT_PATHS = false;
bool VERBOSE = false;
bool SILENT = false;
bool OUTPUT_CUT = false;
string OUTPUT_FILE;
// END PARAMETERS

const double MICROSECS = 1000000.0;

struct InputConfiguration {
    bool load_from_file = false;

    string file_name = "";

    size_t n_nodes_to_generate;
    enum { LARGE } type;
};

struct Configuration {
    InputConfiguration input;
    bool compare_partition = false;
    string partition_file = "";
    bool seed_randomness = false;
    int seed;
    int max_rounds;

    bool show_help_and_exit = false;
    bool use_H_phi_target = false;
    double H_phi_target = 0;
    bool use_G_phi_target = false;
    double G_phi_target = 0;
    // we only break if we find a good enough cut that is also this balanced (has this minside volume)
    bool use_volume_treshold = false;
    double volume_treshold_factor = 0;
};


struct GraphContext {
public:
G g;
vector<Node> nodes;
Cut reference_cut;
long num_edges;
private:
};

using GraphContextp = unique_ptr<GraphContext>;

struct RoundReport {
size_t index;
size_t capacity_required_for_full_flow;
double multi_h_expansion;
double g_expansion;
long volume;
bool relatively_balanced;
Cutp cut;
};

// TODO
// 2) Adapt a stopping routine for H-phi tracking

template <class G>
struct CutStats {
using Node = typename G::Node;
using Edge = typename G::Edge;
using Cut = set<Node>;
using EdgeIt = typename G::EdgeIt;
using Bisection = set<Node>;
size_t crossing_edges = 0;
private:
bool is_min_side;
size_t min_side = 0;
size_t cut_volume = 0;
size_t max_side = 0;
size_t num_edges = 0;
long degreesum() { return num_edges*2;}
long noncut_volume () { return degreesum() - cut_volume;}
public:

CutStats(const G &g, size_t num_vertices, const Cut &cut) {
    initialize(g, num_vertices, cut);
}

void initialize(const G &g, size_t num_vertices, const Cut &cut) {
    for (EdgeIt e(g); e != INVALID; ++e) {
        ++num_edges;
        if (is_crossing(g, cut, e)) crossing_edges += 1;
        if (any_in_cut(g, cut, e)) cut_volume += 1;
    }

    assert(cut.size() <= num_vertices);
    size_t other_size = num_vertices - cut.size();
    min_side = min(cut.size(), other_size);
    max_side = max(cut.size(), other_size);
    is_min_side = cut.size() == min_side;
}

static bool is_crossing(const G &g, const Bisection &c, const Edge &e) {
    bool u_in = c.count(g.u(e));
    bool v_in = c.count(g.v(e));
    return u_in != v_in;
}

static bool any_in_cut(const G &g, const Bisection &c, const Edge &e) {
    bool u_in = c.count(g.u(e));
    bool v_in = c.count(g.v(e));
    return u_in || v_in;
}

long minside_volume() {
    return is_min_side ? cut_volume : noncut_volume();
}

long maxside_volume() {
    return is_min_side ? noncut_volume() : cut_volume;
}

size_t diff() {
    return max_side - min_side;
}

size_t num_vertices() {
    return min_side + max_side;
}

double imbalance() {
    return diff() * 1. / num_vertices();
}

double expansion() {
    return min_side == 0 ? 0 : crossing_edges * 1. / min_side;
}

void print() {
    cout << "Edge crossings (E) : " << crossing_edges << endl;
    cout << "cut size: (" << min_side << " | " << max_side << ")" << endl
         << "diff: " << diff() << " (" << imbalance() << " of total n vertices)" << endl;
    cout << "Min side: " << min_side << endl;
    cout << "E/min(|S|, |comp(S)|) = " << expansion() << endl;
}
};
// Reads the file filename,
// creates that graph in graph g which is assumed to be empty
// In the process fills nodes with each node created at the index of (its id in the file minus one)
// And sets each node's original_ids id to be (its id in the file minus one).
// Of course original_ids must be initialized onto the graph g already earlier.
static void parse_chaco_format(const string &filename, ListGraph &g, vector<Node> &nodes) {
assert(nodes.empty());
if(!SILENT) cout << "Reading graph from " << filename << endl;
ifstream file;
file.open(filename);
if (!file) {
    cerr << "Unable to read file " << filename << endl;
    exit(1);
}

string line;
stringstream ss;
getline(file, line);
ss.str(line);

int n_verts, n_edges;
ss >> n_verts >> n_edges;
if(!SILENT) cout << "Reading a graph with V " << n_verts << "E " << n_edges << endl;
g.reserveNode(n_verts);
g.reserveNode(n_edges);

for (size_t i = 0; i < n_verts; i++) {
    Node n = g.addNode();
    nodes.push_back(n);
}

for (size_t i = 0; i < n_verts; i++) {
    getline(file, line);
    ss.clear();
    ss << line;
    Node u = nodes[i];
    size_t v_name;
    while (ss >> v_name) {
        Node v = nodes[v_name - 1];
        if (findEdge(g, u, v) == INVALID) {
            g.addEdge(u, v);
        }
    }
}

if (n_verts % 2 != 0) {
    if(!SILENT) cout << "Odd number of vertices, adding extra one." << endl;
    Node n = g.addNode();
    g.addEdge(nodes[0], n);
    nodes.push_back(n);
}
}

void generate_large_graph(G &g, vector<Node> &nodes, size_t n_nodes) {
assert(n_nodes > 0);
nodes.reserve(n_nodes);
for (int i = 0; i < n_nodes; i++) {
    nodes.push_back(g.addNode());
}

g.addEdge(nodes[0], nodes[1]);
g.addEdge(nodes[1], nodes[2]);
g.addEdge(nodes[2], nodes[0]);

int lim1 = n_nodes / 3;
int lim2 = 2 * n_nodes / 3;

for (int i = 3; i < lim1; i++) {
    ListGraph::Node u = nodes[i];
    ListGraph::Node v = nodes[0];
    g.addEdge(u, v);
}
for (int i = lim1; i < lim2; i++) {
    ListGraph::Node u = nodes[i];
    ListGraph::Node v = nodes[1];
    g.addEdge(u, v);
}
for (int i = lim2; i < n_nodes; i++) {
    ListGraph::Node u = nodes[i];
    ListGraph::Node v = nodes[2];
    g.addEdge(u, v);
}
}

void write_cut(const vector<Node> &nodes, const Cut &cut) {
ofstream file;
file.open(OUTPUT_FILE);
if (!file) {
    cout << "Cannot open file " << OUTPUT_FILE << endl;
    return;
}

cout << "Writing partition with "
     << nodes.size()
     << " nodes to file "
     << OUTPUT_FILE
     << endl;
for (const auto &n : nodes) {
    file << (cut.count(n) ? "1" : "0") << "\n";
}
file.close();
}

void read_partition_file(const string &filename, const vector<Node> &nodes, Cut &partition) {
ifstream file;
file.open(filename);
if (!file) {
    cerr << "Unable to read file " << filename << endl;
    exit(1);
}
bool b;
size_t i = 0;
while (file >> b) {
    if (b) partition.insert(nodes[i]);
    ++i;
}
if (VERBOSE) cout << "Reference patition size: " << partition.size() << endl;
}

void initGraph(GraphContext &gc, InputConfiguration config) {
    if (config.load_from_file) {
        parse_chaco_format(config.file_name, gc.g, gc.nodes);

    } else {
        if (VERBOSE) cout << "Generating graph with " << config.n_nodes_to_generate << " nodes." << endl;
        generate_large_graph(gc.g, gc.nodes, config.n_nodes_to_generate);
    }

    gc.num_edges = countEdges(gc.g);
}

// For some reason lemon returns arbitrary values for flow, the difference is correct tho
inline
int flow(
        const ArcLookUp<G> &alp,
        const unique_ptr<Preflow<G, EdgeMapi>> &f,
        Node u,
        Node v
) {
    return f->flow(alp(u, v)) - f->flow(alp(v, u));
}

void print_end_round_message(int i) {
    if (VERBOSE) cout << "======================" << endl;
    if(!SILENT) cout << "== End round " << i << " ==" << endl;
    if (VERBOSE) cout << "======================" << endl;
}

void print_matching(const Matchingp &m) {
    for (Matching::EdgeIt e(*m); e != INVALID; ++e) {
        cout << "(" << m->id(m->u(e)) << ", " << m->id(m->v(e)) << "), ";
    }
    cout << endl;
}

void print_cut(const Bisection &out_cut) {
    for (Node n : out_cut) {
        cout << G::id(n) << ", ";
    }
    cout << endl;
}

struct CutMatching {
    const Configuration &config;
    GraphContext &gc;
    default_random_engine &random_engine;
    vector<unique_ptr<RoundReport>> past_rounds;
    vector<Matchingp> matchings;
    bool reached_H_target = false;
    // Input graph
    CutMatching(GraphContext &gc, const Configuration &config_, default_random_engine &random_engine_)
    :
    config(config_),
    gc(gc),
    random_engine(random_engine_)
    {
        assert(gc.nodes.size() % 2 == 0);
        assert(gc.nodes.size() > 0);
        assert(connected(gc.g));
    };

    // During the matching step a lot of local setup is actually made, so it makes sense to group it
    // inside a "matching context" that exists for the duration of the mathing step
    struct MatchingContext {
        G &g;
        Node s;
        Node t;
        EdgeMapi capacity;
        CutMap cut_map;
        const size_t num_vertices;
        Snapshot snap; //RAII

        explicit MatchingContext(G &g_, size_t num_vertices_)
                : g(g_),
                  capacity(g_),
                  cut_map(g_),
                  snap(g_),
                  num_vertices(num_vertices_) {}

        ~MatchingContext() {
            snap.restore();
        }

        bool touches_source_or_sink(Edge &e) {
            return this->g.u(e) == s
                   || this->g.v(e) == s
                   || this->g.u(e) == t
                   || this->g.v(e) == t;
        }

        // Fills given cut pointer with a copy of the cut map
        Cutp extract_cut() {
            Cutp cut(new Cut);
            for (NodeIt n(this->g); n != INVALID; ++n) {
                if (n == s || n == t) continue;
                if (cut_map[n]) cut->insert(n);
            }
            return move(cut);
        }

        void reset_cut_map() {
            for (NodeIt n(this->g); n != INVALID; ++n) {
                cut_map[n] = false;
            }
        }
    };

    struct MatchResult {
        Cutp cut_from_flow;
        // First capacity (minumum) that worked to get full flow thru
        size_t capacity;
    };

    // Soooooo, we want to develop the partition comparison stuff.

    inline void extract_path_fast(
            const G &g,
            const unique_ptr<Preflow<G, EdgeMapi>> &f,
            NodeNeighborMap &flow_children,
            Node u_orig,
            Node t, // For assertsions
            array<Node, 2> &out_path
    ) {
        out_path[0] = u_orig;
        Node u = u_orig;

        assert (flow_children[u].size() > 0);
        while (true) {
            auto &tup = flow_children[u].back();
            Node v = get<0>(tup);
            --get<1>(tup);

            if (get<1>(tup) == 0) {
                flow_children[u].pop_back();
            }

            if (flow_children[v].empty()) {
                if (PRINT_PATHS) {
                    cout << "Path: " << g.id(u_orig);
                }
                assert(v == t);
                assert(u != u_orig);
                out_path[1] = u;
                if (PRINT_PATHS) cout << endl;
                break;
            }

            if (PRINT_PATHS) cout << " -> " << g.id(v);
            u = v;
        }
    }

    void decompose_paths_fast(const MatchingContext &mg, const unique_ptr<FlowAlgo> &f, Paths &out_paths) {
        f->startSecondPhase();
        EdgeMapi subtr(mg.g, 0);
        NodeNeighborMap flow_children(mg.g, vector<tuple<Node, int>>());
        out_paths.reserve(countNodes(mg.g) / 2);

        // Calc flow children (one pass) 
        ArcLookup alp(mg.g);
        for (EdgeIt e(mg.g); e != INVALID; ++e) {
            Node u = mg.g.u(e);
            Node v = mg.g.v(e);
            long e_flow = flow(alp, f, u, v);
            if (e_flow > 0) {
                flow_children[u].push_back(tuple(v, e_flow));
            } else if (e_flow < 0) {
                flow_children[v].push_back(tuple(u, -e_flow));
            }
        }

        for (IncEdgeIt e(mg.g, mg.s); e != INVALID; ++e) {
            assert(mg.g.u(e) == mg.s || mg.g.v(e) == mg.s);
            Node u = mg.g.u(e) == mg.s ? mg.g.v(e) : mg.g.u(e);
            out_paths.push_back(array<Node, 2>());
            extract_path_fast(mg.g, f, flow_children, u, mg.t, out_paths[out_paths.size() - 1]);
        }

    }

    MatchResult bin_search_flows(MatchingContext &mg, unique_ptr<FlowAlgo> &p) const {
        // TODO Output cut
        auto start = high_resolution_clock::now();

        size_t cap = 1;
        for (; cap < mg.num_vertices; cap *= 2) {
            for (EdgeIt e(mg.g); e != INVALID; ++e) {
                if (mg.touches_source_or_sink(e)) continue;
                mg.capacity[e] = cap;
            }

            p.reset(new Preflow<G, EdgeMapi>(mg.g, mg.capacity, mg.s, mg.t));

            if(!SILENT) cout << "Cap " << cap << " ... " << flush;

            auto start2 = high_resolution_clock::now();
            p->runMinCut(); // Note that "startSecondPhase" must be run to get flows for individual verts
            auto stop2 = high_resolution_clock::now();
            auto duration2 = duration_cast<microseconds>(stop2 - start2);

            if(!SILENT) cout << "flow: " << p->flowValue() << " (" << (duration2.count() / MICROSECS) << " s)" << endl;
            if (p->flowValue() == mg.num_vertices / 2) {
                if (VERBOSE) cout << "We have achieved full flow, but half this capacity didn't manage that!" << endl;
                // Already an expander I guess?
                if (cap == 1) {
                    // TODO code duplication
                    mg.reset_cut_map();
                    p->minCutMap(mg.cut_map);
                }
                break;
            }

            // So it will always have the mincutmap of "before"
            // recomputed too many times of course but whatever
            mg.reset_cut_map();
            p->minCutMap(mg.cut_map);
        }

        // Not we copy out the cut
        MatchResult result{mg.extract_cut(), cap};

        auto stop = high_resolution_clock::now();
        auto duration = duration_cast<microseconds>(stop - start);
        if(!SILENT) cout << "Flow search took (seconds) " << (duration.count() / 1000000.0) << endl;

        return result;
    }

    void decompose_paths(const MatchingContext &mg, const unique_ptr<FlowAlgo> &p, vector<array<Node, 2>> &paths) {
        decompose_paths_fast(mg, p, paths);
    }

    void make_sink_source(MatchingContext &mg, const set<Node> &cut) const {
        G &g = mg.g;
        mg.s = g.addNode();
        mg.t = g.addNode();
        int s_added = 0;
        int t_added = 0;
        for (NodeIt n(g); n != INVALID; ++n) {
            if (n == mg.s) continue;
            if (n == mg.t) continue;
            Edge e;
            if (cut.count(n)) {
                e = g.addEdge(mg.s, n);
                s_added++;
            } else {
                e = g.addEdge(n, mg.t);
                t_added++;
            }
            mg.capacity[e] = 1;
        }
        assert(s_added == t_added);
    }

    // Actually, cut player gets H
// Actually Actually, sure it gets H but it just needs the matchings...
    template<typename M>
    Bisectionp cut_player(const G &g, const vector<unique_ptr<M>> &matchings, double &h_multi_exp_out) {
        if (VERBOSE) cout << "Running Cut player" << endl;
        using MEdgeIt = typename M::EdgeIt;

        NodeMapd probs(g);
        vector<Node> all_nodes;

        uniform_int_distribution<int> uniform_dist(0, 1);
        for (NodeIt n(g); n != INVALID; ++n) {
            all_nodes.push_back(n);
            probs[n] = uniform_dist(random_engine)
                       ? 1.0 / all_nodes.size()
                       : -1.0 / all_nodes.size();
        }

        size_t num_vertices = all_nodes.size();

        ListEdgeSet H(g);
        ListEdgeSet H_single(g);
        for (const unique_ptr<M> &m : matchings) {
            for (MEdgeIt e(*m); e != INVALID; ++e) {
                Node u = m->u(e);
                Node v = m->v(e);
                double avg = probs[u] / 2 + probs[v] / 2;
                probs[u] = avg;
                probs[v] = avg;

                H.addEdge(u, v);
                // Updating H_single
                if(findEdge(H_single, u, v) == INVALID) {
                    assert(findEdge(H_single, v, u) == INVALID);
                    H_single.addEdge(u, v);
                }
            }
        }

        sort(all_nodes.begin(), all_nodes.end(), [&](Node a, Node b) {
            return probs[a] < probs[b];
        });

        size_t size = all_nodes.size();
        assert(size % 2 == 0);
        all_nodes.resize(size / 2);
        auto b = Bisectionp(new Bisection(all_nodes.begin(), all_nodes.end()));
        if (VERBOSE) {
            cout << "Cut player gave the following cut: " << endl;
            print_cut(*b);
        }

        auto hcs = CutStats<decltype(H)>(H, num_vertices, *b);
        if (!SILENT) cout << "H expansion: " << hcs.expansion() << ", num cross: " << hcs.crossing_edges << endl;
        h_multi_exp_out = hcs.expansion();
        auto hscs = CutStats<decltype(H_single)>(H_single, num_vertices, *b);
        if (!SILENT) cout << "H_single expansion: " << hscs.expansion() << ", num cross: " << hscs.crossing_edges << endl;

        return b;
    }

    // returns capacity that was required
// Maybe: make the binsearch an actual binsearch
    MatchResult matching_player(G& g, size_t num_vertices, const set<Node> &bisection, ListEdgeSet<G> &m_out) {
        MatchingContext mg(g, num_vertices);
        make_sink_source(mg, bisection);

        unique_ptr<FlowAlgo> p;
        MatchResult mr = bin_search_flows(mg, p);
        if (!SILENT) cout << "Bin search flows done" << endl;
        vector<array<Node, 2>> paths;
        decompose_paths(mg, p, paths);

        for (auto &path : paths) {
            m_out.addEdge(path[0], path.back());
        }
        // Now how do we extract the cut?
        // In this version, in one run of the matching the cut is strictly decided. We just need
        // to decide which one of them.
        // Only when we change to edge will the cut need to be explicitly extracted.
        // Rn the important thing is to save cuts between rounds so I can choose the best.

        return mr;
    }

    long volume_treshold() {
        return config.volume_treshold_factor * gc.num_edges;
    }

    unique_ptr<RoundReport> one_round() {
        unique_ptr<RoundReport> report = make_unique<RoundReport>();
        Bisectionp bisection = cut_player(gc.g, matchings, report->multi_h_expansion);

        Matchingp matchingp(new Matching(gc.g));

        if (VERBOSE) cout << "Running Matching player" << endl;
        MatchResult mr = matching_player(gc.g, gc.nodes.size(), *bisection, *matchingp);
        size_t cap = mr.capacity;
        if (VERBOSE) {
            cout << "Matching player gave the following matching: " << endl;
            print_matching(matchingp);
        }

        matchings.push_back(move(matchingp));
        //c.cuts.push_back(move(mr.cut_from_flow));
        report->index = past_rounds.size();
        report->capacity_required_for_full_flow = cap;
        report->cut = move(mr.cut_from_flow);
        auto cs = CutStats<G>(gc.g, gc.nodes.size(), *report->cut);
        report->g_expansion = cs.expansion();
        if (!SILENT) cout << "G cut expansion " << report->g_expansion << endl;
        report->volume = cs.minside_volume();
        if (!SILENT) cout << "G cut minside volume " << cs.minside_volume() << endl;
        if (!SILENT) cout << "G cut maxside volume " << cs.maxside_volume() << endl;
        report->relatively_balanced = report->volume > volume_treshold();
        return move(report);

        // We want to implement that it parses partitions
        // That has nothing to do with the rounds lol
    }


    // Stopping condition
    bool should_stop() {
        int i = past_rounds.size();
        if(i == 0) return false;
        if(i >= config.max_rounds && config.max_rounds != 0) return true;

        const auto& last_round = past_rounds[past_rounds.size() - 1];
        if(config.use_H_phi_target && last_round->multi_h_expansion >= config.H_phi_target) {
            cout << "H Expansion target reached, this will be case 1 or 3. According to theory, this means we probably won't find a better cut. That is, assuming you set H_phi right. "
                    "If was used together with G_phi target, this also certifies the input graph is a G_phi expander unless there was a very unbaanced cut somewhere, which we will proceed to look for." << endl;
            reached_H_target = true;
            return true;
        }

        if(config.use_volume_treshold && last_round->relatively_balanced) {
            //cout << relatively_balanced << " relatively balanced" << "\n";
            cout << "CASE2 G Expansion target reached with a cut that is relatively balanced. Cut-matching game has found a balanced cut as good as you wanted it."
                 << endl;
            return true;
        }

        //if(config.use_G_phi_target)
        if(last_round->g_expansion >= config.G_phi_target) {
            if(config.use_volume_treshold && last_round->relatively_balanced) {
                //cout << relatively_balanced << " relatively balanced" << "\n";
                cout << "CASE2 G Expansion target reached with a cut that is relatively balanced. Cut-matching game has found a balanced cut as good as you wanted it."
                     << endl;
                return true;
            }

            if(!config.use_volume_treshold) {
                cout << "G Expansion target reached. Cut-matching game has found a cut as good as you wanted it. Whether it is balanced or not is up to you."
                     << endl;
                return true;
            }
        }
    return false;
    }

    void run() {
        cout << "VOlum treshold: " << volume_treshold() << endl;
        cout << "VOlum tresholdf: " << config.volume_treshold_factor << endl;
        // TODO refactor to have "run" be on some stopping condition
        // Documenting everything, and then presentation chooses however it wants.
        while (!should_stop()) {
            past_rounds.push_back(one_round());
            print_end_round_message(past_rounds.size()-1);
        }
    }
};

// TODO Make cut always the smallest
// TODO Implement breaking-logik for unbalance
// om vi hittar phi-cut med volym obanför treshold
// Om vi hittar phi-cut med volum under treshold, så ingorerar vi det och kör p
// och sen om vi når H, då definieras det bästa som phi-cuttet med högsta volym
cxxopts::Options create_options() {
    cxxopts::Options options("executable_name",
                             "Individual project implementation of thatchapon's paper to find graph partitions. Currently only cut-matching game. \
                             \nRecommended usage: \n\texecutable_name -s -f ./path/to/graph -o output.txt\
                             \nCurrently only running a fixed amount of rounds is supported, but the more correct \
                             \nversion of running until H becomes an expander is coming soon.\
                             ");
    options.add_options()
            ("h,help", "Show help")
            ("H_phi", "Phi expansion treshold for the H graph. Recommend to also set -r=0. ",
             cxxopts::value<double>()->implicit_value("10.0"))
            ("G_phi", "Phi expansion target for the G graph. Means \"what is a good enough cut?\" Recommended with -r=0. This is the PHI from the paper. ",
             cxxopts::value<double>()->implicit_value("0.8"))
            ("vol", "Volume treshold. Only used if G_phi is used. Will be multiplied by number of edges, so to require e.g. minimum 10% volume, write 0.1.",
             cxxopts::value<double>()->implicit_value("0.1"))
            ("f,file", "File to read graph from", cxxopts::value<std::string>())
            ("r,max-rounds", "Number of rounds after which to stop (0 for no limit)", cxxopts::value<long>()->default_value("25"))
            ("s,seed", "Use a seed for RNG (optionally set seed manually)",
             cxxopts::value<int>()->implicit_value("1337"))
            ("p,partition", "Partition file to compare with", cxxopts::value<std::string>())
            ("o,output", "Output computed cut into file. The cut is written as the vertices of one side of the cut.", cxxopts::value<std::string>())
            ("n,nodes", "Number of nodes in graph to generate. Should be even. Ignored if -f is set.",
             cxxopts::value<long>()->default_value("100"))
            ("S,Silent", "Only output one line of summary at the end")
            ("v,verbose", "Debug; Whether to print nodes and cuts Does not include paths. Produces a LOT of output on large graphs.")
            ("d,paths", "Debug; Whether to print paths")
            ;
    return options;
}

void parse_options(int argc, char **argv, Configuration &config) {
    auto cmd_options = create_options();
    auto result = cmd_options.parse(argc, argv);

    if (result.count("help")) {
        config.show_help_and_exit = true;
        cout << cmd_options.help() << endl;
    }
    if( result.count("H_phi")) {
        config.use_H_phi_target = true;
        config.H_phi_target = result["H_phi"].as<double>();
    }
    if( result.count("G_phi")) {
        config.use_G_phi_target = true;
        config.G_phi_target = result["G_phi"].as<double>();
    }
    if( result.count("vol")) {
        config.use_volume_treshold = true;
        config.volume_treshold_factor = result["vol"].as<double>();
    }
    if (result.count("file")) {
        config.input.load_from_file = true;
        config.input.file_name = result["file"].as<string>();
    }
    if (result.count("nodes"))
        assert(config.input.load_from_file == false);
        config.input.n_nodes_to_generate = result["nodes"].as<long>();
    if (result.count("max-rounds"))
        config.max_rounds = result["max-rounds"].as<long>();
    if (result.count("verbose"))
        VERBOSE = result["verbose"].as<bool>();
    if (result.count("Silent"))
        SILENT = result["Silent"].as<bool>();
    if (result.count("paths"))
        PRINT_PATHS = result["paths"].as<bool>();

    if (result.count("seed")) {
        config.seed_randomness = true;
        config.seed = result["seed"].as<int>();
    }

    if (result.count("output")) {
        OUTPUT_CUT = true;
        OUTPUT_FILE = result["output"].as<string>();
    }
    if (result.count("partition")) {
        config.compare_partition = true;
        config.partition_file = result["partition"].as<string>();
    }
}

// TODO Selecting best cut not only hightest cap
// TODO extract graph creation from algo
// TODO extract final answer presentation from algo


using CutMap = NodeMap<bool>;



void unit_flow(const ListDigraph &g, double h, ListDigraph::NodeMap<double> &sink_node_cap, ListDigraph::ArcMap<double> &cross_edge_source,
               ListDigraph::ArcMap<double> &flow, ListDigraph::NodeMap<double> &node_flow, ListDigraph::NodeMap<int> &degree,
               ListDigraph::ArcMap<double> &edge_cap, vector<list<ListDigraph::Node>> &level_queue, ListDigraph::NodeMap<int> &node_label) {
    bool excess_flow = true;
    unit_start:
    while (excess_flow) {
        excess_flow = false;
        for (int level_iter = 0; level_iter < h - 1; level_iter++) {
            for (auto list_it = level_queue[level_iter].cbegin(); list_it != level_queue[level_iter].cend(); ++list_it) {
                if (node_flow[*list_it] > sink_node_cap[*list_it]) {  //Push-relabel(v)
                    excess_flow = true;
                    for (ListDigraph::OutArcIt e(g, *list_it); e!=INVALID; ++e) {
                        if (node_label[g.target(e)] == level_iter - 1 && edge_cap[e] - flow[e] > 0) {
                            // push
                            double ex = node_flow[g.target(e)];
                            double rf = flow[e] - edge_cap[e];
                            double deg_minus_ex = degree[*list_it] - ex;
                            double phi = min(ex, min(rf, deg_minus_ex));
                            flow[e] += phi;
                            flow[e] -= phi;                         
                            node_flow[*list_it] -= phi;
                            node_flow[g.target(e)] += phi;
                            //don't relabel
                        }
                        else {
                            //Relabel v += 1
                            node_label[*list_it] += 1;
                            level_queue[level_iter].erase(list_it);
                            level_queue[level_iter + 1].push_back(*list_it);
                        }
                        goto unit_start;
                    }
                }
            }
        }

     
    }
}

void local_flow(const G &ug, const ListDigraph &g, set<Node> set_A, double phi, int v, int e) {

    struct flow_instance {
        int v = 0;
        int e = 0;
        EdgeMap<double> cross_edge_source(G);
        EdgeMap<double> edge_cap(G);
        NodeMap<double> sink_node_cap(G);
        NodeMap<int> degree(G);
        NodeMap<bool> cut_map;

        flow_instance(int v, int e, EdgeMap<double> &cross_edge_source(G), EdgeMap<double> &edge_cap(G),
                      NodeMap<double> &sink_node_cap(G), NodeMap<int> &degree(G), NodeMap<bool> &cut_map(G));
    };

    // INITIALIZE ALL

    ListDigraph::ArcMap<double> cross_edge_source(g); 
    ListDigraph::ArcMap<double> edge_cap(g);
    ListDigraph::ArcMap<double> flow(g);
    ListDigraph::NodeMap<double> sink_node_cap(g);
    ListDigraph::NodeMap<int> degree(g);
    ListDigraph::NodeMap<int> node_label(g);
    ListDigraph::NodeMap<bool> A(g, false);
    ListDigraph::NodeMap<double> node_flow(g);

    double h = 1 / (phi * log2(e));
    vector<list<ListDigraph::Node>> level_queue;
    for (int i = 0; i < h; i++) {
        level_queue.push_back(list<ListDigraph::Node>());
    }

    for (NodeIt i(ug); i!=INVALID; ++i) {
        ListDigraph::Node n = g.nodeFromId(ug.id(i));
        if (set_A.count(i)) {
            A[n] = true;
            level_queue[0].push_back(n);
            node_label[n] = 0;
        }
        else {
            A[n] = false;
        } 
        node_flow[n] = 0;
    }
    for (ListDigraph::ArcIt i(g); i!=INVALID; ++i) {
        if (A[g.source(i)] && !A[g.target(i)]) {
            cross_edge_source[i] = 2/phi;
            edge_cap[i] = 2/phi;
        }
        else if (!A[g.source(i)] && A[g.target(i)]) {
            cross_edge_source[i] = 2/phi;
            edge_cap[i] = 2/phi;
        }
        else {
            //cross_edge_source[i] = 0;
            //edge_cap[i] = 0;
        }
        degree[g.source(i)] += 1;
        degree[g.target(i)] += 1;
        flow[i] = 0;
    }

    for (ListDigraph::NodeIt i(g); i!=INVALID; ++i) {
        if (A[i])
            sink_node_cap[i] = degree[i];
    }
    
    bool found_feasible_routing = false;

    while (!found_feasible_routing) {
        cout << "Calling unit flow \n";
        unit_flow(g, h, sink_node_cap,
                  cross_edge_source,
                  flow,
                  node_flow,
                  degree,
                  edge_cap,
                  level_queue,
                  node_label); 

        if (level_queue[h-1].empty())
            break;

        int i_ = 0;
        for (int i = h - 1; i > 0; --i) {
            for (auto node = level_queue[i].cbegin(); node != level_queue[i].cend(); ++node) {
                int edges_to_next_level = 0;
                int edges_to_any_level  = 0;
                //r (ListDigraph::OutArcIt e(g, *list_it); e!=INVALID; ++e)
                for (ListDigraph::OutArcIt a(g, *node); a!=INVALID; ++a) {
                    edges_to_any_level++;
                    if (node_label[g.target(a)])
                        edges_to_next_level++;
                }
                if (0 < edges_to_next_level <= 5 * edges_to_any_level * log2(e) / h) {
                    goto level_cut;
                    i_ = i;
                }
            }
        }
        break;
    level_cut:
        int n_upper_queue_nodes = 0;
        int n_lower_queue_nodes = 0;
        for (int j = h - 1; j > i_; --j)
            n_upper_queue_nodes += level_queue[j].size();
        for (int j = i_ - 1; j > 0; --j)
            n_upper_queue_nodes += level_queue[j].size();;

        if (n_upper_queue_nodes < n_lower_queue_nodes)
            for (int j = i_ - 1; j > 0; --j)
                level_queue[j].clear();
        else
            for (int j = h - 1; j > i_; --j)
                level_queue[j].clear();
    }

   set_A.clear();
   for (int i = h - 1; i > 0; --i) {
        for (auto node = level_queue[i].cbegin(); node != level_queue[i].cend(); ++node) {
            set_A.insert(ug.nodeFromId(g.id(*node)));
        }
    }
    return;
}


ListDigraph *digraph_from_graph(G &g, ListDigraph &dg) {

    for(NodeIt n(g); n!=INVALID; ++n)
        dg.addNode();

    for(EdgeIt a(g); a!=INVALID; ++a) {
        dg.addArc(dg.nodeFromId(g.id(g.u(a))), dg.nodeFromId(g.id(g.v(a))));
        dg.addArc(dg.nodeFromId(g.id(g.v(a))), dg.nodeFromId(g.id(g.u(a))));
    }

    return &dg;
}


map<Node, Node> graph_from_cut(G &g, GraphContext &sg, set<Node> cut, map<Node, Node> old_map, bool complement=false) {
    map<Node, Node> new_map = map<Node, Node>();
    map<Node, Node> reverse_map = map<Node, Node>();
    set<Node> all_nodes = set<Node>();
    set<Node> complement_nodes = set<Node>();
    sg.num_edges = 0;
    assert (sg.nodes.size() == 0);
    
    if (complement == true) {
        for (NodeIt n(g); n!=INVALID; ++n) {
            all_nodes.insert(n);
        }
        //cut.clear();
        std::set_difference(all_nodes.begin(), all_nodes.end(), cut.begin(), cut.end(),
                std::inserter(complement_nodes, complement_nodes.end()));
        cut.swap(complement_nodes);
    }

    for (auto n : cut) {
        Node x = sg.g.addNode();
        sg.nodes.push_back(x);
        //Maybe not necessary
        new_map[x] = old_map[n];
        reverse_map[n] = x;
    }
    //sort(sg.nodes.begin(), sg.nodes.end());

    for (const auto &n : cut) {
        for (OutArcIt a(g, n); a!=INVALID; ++a) {
            if (cut.count(g.target(a)) > 0 && reverse_map[n] < reverse_map[g.target(a)]) { //Edge inside cut
                assert (reverse_map[n] != reverse_map[g.target(a)]);
                assert (sg.g.id(reverse_map[g.source(a)]) < sg.nodes.size() && sg.g.id(reverse_map[g.target(a)]) < sg.nodes.size());
                sg.g.addEdge(reverse_map[n], reverse_map[g.target(a)]);
                sg.num_edges++;
            }
            //Add self-nodes ?
    }   }

    return new_map;
}


void graph_to_component_subgraphs(ListGraph g, NodeMap<Node> map_to_original_graph) {
    vector<GraphContextp> subgraphs;
    int c = 0;
    Bfs<ListGraph> bfs(g);
    bfs.init();
    //GraphContext G_1;
    vector<unique_ptr<NodeMap<Node>>> reverse_maps;
    vector<unique_ptr<NodeMap<Node>>> maps_to_orig;
    subgraphs.push_back(make_unique<GraphContext>());
    reverse_maps.push_back(make_unique<NodeMap<Node>>((*subgraphs[0]).g));
    maps_to_orig.push_back(make_unique<NodeMap<Node>>((*subgraphs[0]).g));
    for(NodeIt v(g); v != INVALID; ++v) {
        Node x = (*subgraphs[c]).g.addNode();
        (*reverse_maps[c])[x] = v;
        (*maps_to_orig[c])[x] = map_to_original_graph[v];
        if(!bfs.reached(v)) {
            c++;
            GraphContext G_i;
            subgraphs.push_back(make_unique<GraphContext>());
            reverse_maps.push_back(make_unique<NodeMap<Node>>((*subgraphs[c]).g));
            maps_to_orig.push_back(make_unique<NodeMap<Node>>((*subgraphs[c]).g));
            bfs.addSource(v);
            bfs.start();
        }
    }
    //Iterate components
    for (int c_ = 0; c_ < c; ++c) {
        for (NodeIt n((*subgraphs[c]).g); n != INVALID; ++n) {
            for (OutArcIt e((*subgraphs[c]).g, n); n!= INVALID; ++n) {
                if ((*subgraphs[c]).g.u(e) < (*subgraphs[c]).g.v(e))
                    (*subgraphs[c]).g.addEdge((*reverse_maps[c])[(*subgraphs[c]).g.u(e)], (*reverse_maps[c])[(*subgraphs[c]).g.v(e)]);
            }
        }
    }
    //No return at the moment
    return;
}


map<Node, Node> connected_subgraph_from_graph(const ListGraph &g, GraphContext &sg, map<Node, Node> map_to_original_graph, NodeIt &it) {

    Bfs<ListGraph> bfs(g);
    bfs.init();
    //bfs.addSource(v);
    //bfs.start();
    bfs.run(it);
    map<Node, Node> reverse_map;
    map<Node, Node> forward_map;
    map<Node, Node> map_to_orig;

    while (it!= INVALID) {
        Node x = sg.g.addNode();
        sg.nodes.push_back(x);
        reverse_map[x] = it;
        forward_map[it] = x;
        map_to_orig[x] = map_to_original_graph[it];
        ++it;
        if (it == INVALID)
            break;
        if(!bfs.reached(it)) {
            cout << "Not connected - creating subgraph" << endl;
            break;
    }   }

    for (NodeIt n(sg.g); n != INVALID; ++n) {
        cout << "Working on node: " << sg.g.id(n) << endl;
        for (OutArcIt e(g, reverse_map[n]); e!= INVALID; ++e) {
            cout << "Arc it" << endl;
            if (g.id(g.target(e)) > g.id(g.source(e)) && forward_map.count(g.source(e)) > 0 && forward_map.count(g.target(e)) > 0 ) {
                cout << "Adding edge between " << sg.g.id(forward_map[g.u(e)]) << " and " << sg.g.id(forward_map[g.v(e)]) << endl;
                sg.g.addEdge(forward_map[g.source(e)], forward_map[g.target(e)]);
                sg.num_edges++;
    }   }   }

    return map_to_orig;
}


vector<map<Node, Node>> decomp(GraphContext &gc, ListDigraph &dg, Configuration config, map<Node, Node> map_to_original_graph, vector<set<Node>> cuts, vector<map<Node, Node>> node_maps_to_original_graph) {

    if (gc.nodes.size() == 1) {
        node_maps_to_original_graph.push_back(map_to_original_graph);
        return node_maps_to_original_graph;
    }

    Node temp_node;
    bool added_node = false;
    if (gc.nodes.size() % 2 != 0) {
        added_node = true;
        temp_node = gc.g.addNode();
        gc.g.addEdge(gc.nodes[0], temp_node);
        gc.nodes.push_back(temp_node);
        gc.num_edges++;
    }

    cout << "init cut-matching" << endl;
    default_random_engine random_engine = config.seed_randomness
                    ? default_random_engine(config.seed)
                    : default_random_engine(random_device()());
    CutMatching cm(gc, config, random_engine);
    cout << "Start cut-matching" << endl;
    cm.run();
    cout << "Finish cut-matching" << endl;
    assert(!cm.past_rounds.empty());
    auto& best_round = *max_element(cm.past_rounds.begin(), cm.past_rounds.end(), [](auto &a, auto &b) {
        return a->g_expansion < b->g_expansion;
    });

    if (added_node) {
        (*(best_round->cut)).erase(temp_node);
        gc.g.erase(temp_node);
    }
    
    cout << "The best with highest expansion was found on round" << best_round->index << endl;
    cout << "Best cut sparsity: " << endl;
    auto &best_cut = best_round->cut;
    CutStats<G>(gc.g, gc.nodes.size(), *best_cut).print();

    if(config.use_H_phi_target && config.use_G_phi_target && config.use_volume_treshold) {
        if(cm.reached_H_target) {
            if(best_round->g_expansion < config.G_phi_target) {
                cout << "CASE1 NO Goodenough cut, G certified expander." << endl;
                node_maps_to_original_graph.push_back(map_to_original_graph);
                cuts.push_back(*(best_round->cut));
            } else {
                ListDigraph dg_;
                digraph_from_graph(gc.g, dg_);
                local_flow(gc.g, dg_, *(best_round->cut), config.G_phi_target, gc.nodes.size(), gc.num_edges);
                cuts.push_back(*best_round->cut);
                GraphContext V_over_A;
                map<Node, Node> new_map = graph_from_cut(gc.g, V_over_A, *(best_round->cut), map_to_original_graph, true);
                node_maps_to_original_graph.push_back(new_map);
                map <Node, Node> new_map_;
                NodeIt n(V_over_A.g);
                while (n != INVALID) {
                    GraphContext V_over_A_;
                    new_map_ = connected_subgraph_from_graph(V_over_A.g, V_over_A_, new_map, n);
                    cout << "Number of nodes is: " << V_over_A_.nodes.size() << " number of edges: " << V_over_A_.num_edges << endl;
                    assert(V_over_A_.num_edges > (V_over_A_.nodes.size() - 2));
                    node_maps_to_original_graph = decomp(V_over_A_, dg, config, new_map_, cuts, node_maps_to_original_graph);
                }
                //decomp(V_over_A, dg, config, map_to_original_graph, cuts, node_maps_to_original_graph);
            }
        } else {
            cout << "CASE2 Goodenough balanced cut" << endl;
            GraphContext A;
            cout << "Create map to original graph" << endl;
            map<Node, Node> new_map = graph_from_cut(gc.g, A, *(best_round->cut), map_to_original_graph);
            assert (A.nodes.size() == (*(best_round->cut)).size());
            cout << "Decomp on A" << endl;
 
            map <Node, Node> new_map_;
            NodeIt n(A.g);
            while (n != INVALID) {
                GraphContext A_;
                new_map_ = connected_subgraph_from_graph(A.g, A_, new_map, n);
                cout << "Number of nodes is: " << A_.nodes.size() << " number of edges: " << A_.num_edges << endl;
                assert(A_.num_edges >= (A_.nodes.size() - 1));
                node_maps_to_original_graph = decomp(A_, dg, config, new_map_, cuts, node_maps_to_original_graph);
            }
            GraphContext R;
            cout << "(R) create map to original graph" << endl;
            new_map = graph_from_cut(gc.g, R, *(best_round->cut), map_to_original_graph, true);
            cout << "Decomp on R" << endl;
            NodeIt n_(R.g);
            while (n_ != INVALID) {
                GraphContext R_;
                new_map_ = connected_subgraph_from_graph(R.g, R_, new_map, n_);
                node_maps_to_original_graph = decomp(R_, dg, config, new_map_, cuts, node_maps_to_original_graph);
            }
            //decomp(R, dg, config, new_map, cuts, node_maps_to_original_graph);
        }
    }
    return node_maps_to_original_graph;
}


            //write_cut(A.nodes, *best_cut);
            //

            //typedef dim2::Point<int> Point;
            //ListGraph::NodeMap<Point> coords(A.g);
            //for (NodeIt n(A.g); n!=INVALID; ++n)
            //    coords[n]=Point(A.g.id(n)*5 % 50, A.g.id(n));
    /*
    graphToEps(A.g,"graph_to_eps_demo_out_1_pure.eps").
    coords(coords).
    title("Sample .eps figure").
    copyright("(C) 2003-2009 LEMON Project").
    run();

  lemon::GraphWriter(A.g, std::cout)
  .run();
    lemon::GraphWriter(gc.g, std::cout)
  .run();
  */


int main(int argc, char **argv) {

    Configuration config = Configuration();
    parse_options(argc, argv, config);

    if(config.show_help_and_exit) return 0;

    GraphContext gc;
    initGraph(gc, config.input);
    ListDigraph dg;
    digraph_from_graph(gc.g, dg);

    map<Node, Node> map_to_original_graph;
    for (NodeIt n(gc.g); n!=INVALID; ++n)
        map_to_original_graph[n] = n;

    vector<set<Node>> cuts = vector<set<Node>>();
    vector<map<Node, Node>> node_maps_to_original_graph = vector<map<Node, Node>>();

    vector<map<Node, Node>> cut_maps = decomp(gc, dg, config, map_to_original_graph, cuts, node_maps_to_original_graph);

    cout << "Done decomp" << endl;
    for (const auto &m : cut_maps) {
        for (const auto &c : m) {
            cout << gc.g.id(c.second) << " ";
        }
        cout << endl;
    } 
    
    return 0;

    default_random_engine random_engine = config.seed_randomness
                    ? default_random_engine(config.seed)
                    : default_random_engine(random_device()());
    CutMatching cm(gc, config, random_engine);
    cm.run();

    // TODO searching conditions different depending on if hit H
    assert(!cm.past_rounds.empty());
    // Best by expnansion
    auto& best_round = *max_element(cm.past_rounds.begin(), cm.past_rounds.end(), [](auto &a, auto &b) {
        return a->g_expansion < b->g_expansion;
    });

    cout << "The best with highest expansion was found on round" << best_round->index << endl;
    cout << "Best cut sparsity: " << endl;
    auto &best_cut = best_round->cut;
    CutStats<G>(gc.g, gc.nodes.size(), *best_cut).print();

    if(config.use_H_phi_target && config.use_G_phi_target && config.use_volume_treshold) {
        if(cm.reached_H_target) {
            if(best_round->g_expansion < config.G_phi_target) {
                cout << "CASE1 NO Goodenough cut, G certified expander." << endl;
                //for (const auto &n : nodes) {
                //file << (cut.count(n) ? "1" : "0") << "\n";
            } else {
                cout << "CASE3 Found goodenough but very unbalanced cut." << endl;
                local_flow(gc.g, dg, *(best_round->cut), config.G_phi_target, gc.nodes.size(), gc.num_edges);
            }
        } else {
            cout << "CASE2 Goodenough balanced cut" << endl;

        }

    }

    cout << "DEBUG LOCAL FLOW" << "\n";
    local_flow(gc.g, dg, *(best_round->cut), config.G_phi_target, gc.nodes.size(), gc.num_edges);
    cout << "FINISHED LOCAL FLOW" << "\n";
    if (OUTPUT_CUT) { write_cut(gc.nodes, *best_cut); }

    if (config.compare_partition) {
        read_partition_file(config.partition_file, gc.nodes, gc.reference_cut);
        cout << endl
             << "The given partition achieved the following:"
             << endl;
        CutStats<G>(gc.g, gc.nodes.size(), gc.reference_cut).print();
    }

    return 0;
}

#pragma clang diagnostic pop
