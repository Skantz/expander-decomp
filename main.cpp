// Authored by Ludvig Janiuk 2019 as part of individual project at KTH.
#pragma clang diagnostic push
#pragma ide diagnostic ignored "cert-msc32-c"
#pragma ide diagnostic ignored "cppcoreguidelines-slicing"

#include <iostream>
#include <ostream>
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

// TODO now
// Clean the code much more, to be able to do the stopping and edge version
// Basically get unnecessary stuff out of the algo

// TODO OK how do we do edge version...
// Whats the plan for hte edge version? Lets describe it in text
// 1. At the start of the algo, we need to make the subdivision graph.
// 2. And we need the set of subivided vertices. we could store it in the context to start with.
// 3. Then cut player needs to do the cut on those instead, can this be cone in an opaque way?
// 4. The matching player has to push flow differently and compile the cut differently. This will be a big difference.


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
template<class T> using EdgeMap = typename G::template EdgeMap<T>;
using EdgeMapi = EdgeMap<int>; // LEMON uses ints internally. We might want to look into this
using EdgeMapb = EdgeMap<bool>; // LEMON uses ints internally. We might want to look into this
template<class T> using NodeMap = typename G::template NodeMap<T>;
using NodeMapi = NodeMap<int>;
using NodeMapb= NodeMap<bool>;
using NodeNeighborMap = NodeMap<vector<tuple<Node, int>>>;
using FlowAlgo = Preflow<G, EdgeMapi>;
using Matching = vector<array<Node, 2>>;
using Matchingp = unique_ptr<Matching>;
using Bisection = set<Node>;
using Bisectionp = unique_ptr<Bisection>;
using Cut = set<Node>;
using Cutp = unique_ptr<Cut>;
using CutMap = NodeMap<bool>;

const double MICROSECS = 1000000.0;
const auto& now = high_resolution_clock::now;
double duration_sec(const high_resolution_clock::time_point& start, high_resolution_clock::time_point& stop) {
    return duration_cast<microseconds>(stop - start).count() / MICROSECS;
}

struct InputConfiguration {
    bool load_from_file = false;
    string file_name = "";
    size_t n_nodes_to_generate;
};

struct Configuration {
    InputConfiguration input;
    bool compare_partition = false;
    string partition_file = "";
    bool seed_randomness = false;
    int seed;
    int max_rounds;
    bool output_cut;
    string output_file;
    bool show_help_and_exit = false;
    bool use_H_phi_target = false;
    double H_phi_target = 0;
    bool use_G_phi_target = false;
    double G_phi_target = 0;
    // we only break if we find a good enough cut that is also this balanced (has this minside volume)
    bool use_volume_treshold = false;
    double volume_treshold_factor = 0;
    double h_factor = 0;
    double h_ratio = 0;
};

struct Logger {
    bool silent = false;
    bool verbose = false;
    ofstream nul; // UNopened file stream, will act like /dev/null
    Logger() : nul() { };
    decltype(cout)& progress() {
        return silent ? nul : cout ;
    };
    decltype(cout)& debug() {
        return verbose ? cout : nul;
    };
} l;

struct GraphContext {
    G g;
    vector<Node> nodes;
    long num_edges;
    map<Node, int> orig_degree;
};
using GraphContextp = unique_ptr<GraphContext>;

// I'd say implementing our own adaptor is more effort, we can just do the snapshot thing
// Actually lets just subdivide manually at the start and we dont even need to restore.
struct SubdividedGraphContext {
    SubdividedGraphContext (GraphContext& gc) :
    origContext(gc),
    nf(sub_g),
    ef(sub_g),
    n_ref(gc.g, INVALID),
    n_cross_ref(sub_g, INVALID),
    origs(sub_g, false), 
    only_splits(sub_g, nf, ef) {} ;


    GraphContext& origContext;
    G sub_g;
    NodeMapb nf;
    EdgeMapb ef;
    NodeMap<Node> n_cross_ref;
    NodeMap<Node> n_ref;
    NodeMap<bool> origs;
    SubGraph<G> only_splits;
    vector<Node> split_vertices;
};

// TODO What chnages will be necessary?
struct RoundReport {
    size_t index;
    size_t capacity_required_for_full_flow;
    double multi_h_conductance;
    double g_conductance;
    long volume;
    bool relatively_balanced;
    Cutp cut;
};

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
        cut_volume = 0;
        crossing_edges = 0;
        for (EdgeIt e(g); e != INVALID; ++e) {
            ++num_edges;
            if (is_crossing(g, cut, e)) crossing_edges += 1;
            //if (any_in_cut(g, cut, e)) cut_volume += 1;
            if (cut.count(g.u(e))) cut_volume += 1;
            if (g.u(e) == g.v(e)) continue;
            if (cut.count(g.v(e))) cut_volume += 1;
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

    double conductance() {
        //Q: changed to 1
        return minside_volume() == 0 ? 1 : crossing_edges * 1. / minside_volume();
    }

    void print() {
        cout << "Edge crossings (E) : " << crossing_edges << endl;
        cout << "cut size: (" << min_side << " | " << max_side << ")" << endl
             << "diff: " << diff() << " (" << imbalance() << " of total n vertices)" << endl;
        cout << "Min side: " << min_side << endl;
        //cout << "E/min(|S|, |comp(S)|) = " << expansion() << endl;
        cout << "expansion: " << expansion() << endl;
        cout << "conductance: " << conductance() << endl;
        cout << "cut volume: " << cut_volume << endl;
        cout << "noncut volume: " << noncut_volume() << endl;
    }
};
// Reads the file filename,
// creates that graph in graph g which is assumed to be empty
// In the process fills nodes with each node created at the index of (its id in the file minus one)
// And sets each node's original_ids id to be (its id in the file minus one).
// Of course original_ids must be initialized onto the graph g already earlier.
static void parse_chaco_format(const string &filename, ListGraph &g, vector<Node> &nodes) {
    assert(nodes.empty());
    l.progress() << "Reading graph from " << filename << endl;
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
    l.progress() << "Reading a graph with V " << n_verts << "E " << n_edges << endl;
    g.reserveNode(n_verts);
    g.reserveNode(n_edges);

    for (size_t i = 0; i < n_verts; i++) {
        Node n = g.addNode();
        nodes.push_back(n);
    }

    for (size_t i = 0; i < n_verts; i++) {
        getline(file, line);


        Node u = nodes[i];
        istringstream iss(line);
        vector<string> tokens{istream_iterator<string>{iss},
                              istream_iterator<string>{}};
        for(string& str : tokens) {
            size_t v_name = stoi(str);
            cout << "edge to: " << v_name << "..." ;
            assert(v_name != 0);
            Node v = nodes[v_name - 1];
            if (findEdge(g, u, v) == INVALID) {
                g.addEdge(u, v);
            }
        }
    }

    if (n_verts % 2 != 0) {
        l.progress() << "Odd number of vertices, adding extra one." << endl;
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

void write_cut(const vector<Node> &nodes, const Cut &cut, string file_name) {
    ofstream file;
    file.open(file_name);
    if (!file) {
        cout << "Cannot open file " << file_name << endl;
        return;
    }

    cout << "Writing partition with "
         << nodes.size()
         << " nodes to file "
         << file_name
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
    l.debug() << "Reference patition size: " << partition.size() << endl;
}

void initGraph(GraphContext &gc, InputConfiguration config) {
    if (config.load_from_file) {
        parse_chaco_format(config.file_name, gc.g, gc.nodes);

    } else {
        l.debug() << "Generating graph with " << config.n_nodes_to_generate << " nodes." << endl;
        generate_large_graph(gc.g, gc.nodes, config.n_nodes_to_generate);
    }

    for (NodeIt n(gc.g); n != INVALID; ++n) {
        for (IncEdgeIt e(gc.g, n); e != INVALID; ++e)
            gc.orig_degree[n] += 1;
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
    l.debug() << "======================" << endl;
    l.progress() << "== End round " << i << " ==" << endl;
    l.debug() << "======================" << endl;
}

template <typename GG>
void print_matching(GG& g, const Matchingp &m, decltype(cout)& stream) {
    for (auto& e : *m) {
        stream << "(" << g.id(e[0]) << ", " << g.id(e[1]) << "), ";
    }
    stream << endl;
}

void print_cut(const Bisection &out_cut, decltype(cout)& stream) {
    for (Node n : out_cut) {
        stream << G::id(n) << ", ";
    }
    stream << endl;
}

void print_graph(G& g, decltype(cout)& stream) {
    stream << "Printing a graph" << endl;
    stream << "Vertices: " << countNodes(g) << ", Edges: " << countEdges(g) << endl;
    stream << "==" << endl;
    for(NodeIt n(g); n != INVALID; ++n) {
        stream << g.id(n) << ", ";
    }
    stream << "\n==" << endl;
    for(EdgeIt e(g); e != INVALID; ++e) {
        stream << g.id(e) << ": " << g.id(g.u(e)) << " - " << g.id(g.v(e)) << "\n";
    }
    stream << endl;
}


// Actually copies the graph.
void createSubdividedGraph(SubdividedGraphContext& sgc) {
    graphCopy(sgc.origContext.g, sgc.sub_g).nodeCrossRef(sgc.n_cross_ref).run();
    graphCopy(sgc.origContext.g, sgc.sub_g).nodeRef(sgc.n_ref).nodeCrossRef(sgc.n_cross_ref).run();
    G& g = sgc.sub_g;
    for (NodeIt n(g); n != INVALID; ++n) {
        sgc.origs[n] = true;
    }
    vector<Edge> edges;
    for (EdgeIt e(g); e != INVALID; ++e) {
        if (g.u(e) != g.v(e))
            edges.push_back(e);
    }

    for (NodeIt n(g); n != INVALID; ++n) {
        sgc.only_splits.disable(n);
    }

    for(auto& e : edges) {
        if (g.u(e) == g.v(e))
            continue;
        Node u = g.u(e);
        Node v = g.v(e);
        g.erase(e);

        Node s = g.addNode();
        sgc.origs[s] = false;
        sgc.only_splits.enable(s);
        g.addEdge(u, s);
        if (u != v) g.addEdge(s, v);


        //if (u !=v)
        sgc.split_vertices.push_back(s);
    }
}

struct CutMatching {
    const Configuration &config;
    GraphContext &gc;
    SubdividedGraphContext sgc;
    default_random_engine &random_engine;
    //vector<unique_ptr<RoundReport>> sub_past_rounds;
    vector<unique_ptr<RoundReport>> sub_past_rounds;
    vector<Matchingp> matchings;
    vector<Matchingp> sub_matchings;
    bool reached_H_target = false;
    // Input graph
    CutMatching(GraphContext &gc, const Configuration &config_, default_random_engine &random_engine_)
    :
    config(config_),
    gc(gc),
    sgc{gc},
    random_engine(random_engine_)
    {
        assert(gc.nodes.size() % 2 == 0);
        assert(gc.nodes.size() > 0);
        cout << "what's going on here n: " << gc.nodes.size() << " e: " << gc.num_edges << endl;
        assert(connected(gc.g));

        createSubdividedGraph(sgc);
    };

    // During the matching step a lot of local setup is actually made, so it makes sense to group it
    // inside a "matching context" that exists for the duration of the mathing step
    struct MatchingContext {
        // This NEEDS to be the whole graph
        G& g;
        Node s;
        Node t;
        EdgeMapi capacity;
        CutMap cut_map;
        Snapshot snap; //RAII

        explicit MatchingContext(G& g_)
        :
        g(g_),
        capacity(g_),
        cut_map(g_),
        snap(g_)
        {}

        ~MatchingContext() {
            snap.restore();
        }

        bool touches_source_or_sink(Edge &e) {
            return g.u(e) == s
                   || g.v(e) == s
                   || g.u(e) == t
                   || g.v(e) == t;
        }

        // Fills given cut pointer with a copy of the cut map
        Cutp extract_cut() {
            Cutp cut(new Cut);
            for (NodeIt n(g); n != INVALID; ++n) {
                if (n == s || n == t) continue;
                if (cut_map[n]) cut->insert(n);
            }
            return move(cut);
        }

        void reset_cut_map() {
            for (NodeIt n(g); n != INVALID; ++n) {
                cut_map[n] = false;
            }
        }
    };

    struct MatchResult {
        Cutp cut_from_flow;
        size_t capacity; // First capacity (minumum) that worked to get full flow thru
    };

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
        int i = 0;
        while (true) {
            i++;
            auto& vv = flow_children[u];
            assert(vv.size() > 0);
            auto &tup = vv.back();
            Node v = get<0>(tup);
            --get<1>(tup);

            if (get<1>(tup) == 0) flow_children[u].pop_back();

            if (flow_children[v].empty()) {
                assert(v == t);
                assert(u != u_orig);

                out_path[1] = u;
                break;
            }

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
            if (mg.g.u(e) == mg.g.v(e))
                continue;
            Node u = mg.g.u(e);
            Node v = mg.g.v(e);
            long e_flow = flow(alp, f, u, v);
            if (e_flow > 0) {
                flow_children[u].push_back(tuple(v, e_flow));
            } else if (e_flow < 0) {
                flow_children[v].push_back(tuple(u, -e_flow));
            }
        }

        for (IncEdgeIt e(mg.g, mg.s); e != INVALID ; ++e) {
            if (mg.g.u(e) == mg.g.v(e))
                continue;
            assert(mg.g.u(e) == mg.s || mg.g.v(e) == mg.s);
            Node u = mg.g.u(e) == mg.s ? mg.g.v(e) : mg.g.u(e);

            out_paths.push_back(array<Node, 2>());
            extract_path_fast(mg.g, f, flow_children, u, mg.t, out_paths[out_paths.size() - 1]);
        }
    }

    // Works for sub too, with the assumption that mg.g realy is the whole graph
    void run_min_cut(const MatchingContext &mg, unique_ptr<FlowAlgo> &p) const {
        p.reset(new Preflow<G, EdgeMapi>(mg.g, mg.capacity, mg.s, mg.t));
        auto start2 = now();
        p->runMinCut(); // Note that "startSecondPhase" must be run to get flows for individual verts
        auto stop2 = now();
        l.progress() << "flow: " << p->flowValue() << " (" << duration_sec(start2, stop2) << " s)" << endl;
    }

    // This should work well for sub too
    void set_matching_capacities(MatchingContext &mg, size_t cap) const {
        for (EdgeIt e(mg.g); e != INVALID; ++e) {
            if (mg.touches_source_or_sink(e)) continue;
            mg.capacity[e] = cap;
        }
    }

    MatchResult bin_search_flows(MatchingContext &mg, unique_ptr<FlowAlgo> &p, size_t flow_target) const {
        auto start = now();
        size_t cap = 1;
        //for (; cap < mg.gc.nodes.size(); cap *= 2) {
        for (; cap < flow_target*2; cap *= 2) {
            l.progress() << "Cap " << cap << " ... " << flush;
            set_matching_capacities(mg, cap);
            run_min_cut(mg, p);

            //bool reachedFullFlow = p->flowValue() == mg.gc.nodes.size() / 2;
            bool reachedFullFlow = p->flowValue() >= flow_target;
            if (reachedFullFlow) l.debug() << "We have achieved full flow, but half this capacity didn't manage that!" << endl;

            // So it will always have the mincutmap of "before"
            // mincuptmap is recomputed too many times of course but whatever
            // If we reached it with cap 1, already an expander I guess?
            // In this case this was never done even once, so we have to do it before breaking
            if (!reachedFullFlow || cap == 1) {
                mg.reset_cut_map();
                p->minCutMap(mg.cut_map);
            }

            if (reachedFullFlow) break;
        }

        // Not we copy out the cut
        MatchResult result{mg.extract_cut(), cap};

        auto stop = now();
        l.progress() << "Flow search took (seconds) " << duration_sec(start, stop) << endl;

        return result;
    }

    void decompose_paths(const MatchingContext &mg, const unique_ptr<FlowAlgo> &p, vector<array<Node, 2>> &paths) {
        decompose_paths_fast(mg, p, paths);
    }

    template <typename GG>
    void make_sink_source(GG& g, MatchingContext &mg, const set<Node> &cut) const {
        mg.s = g.addNode();
        mg.t = g.addNode();
        int s_added = 0;
        int t_added = 0;
        for (typename GG::NodeIt n(g); n != INVALID; ++n) {
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
        int diff = s_added - t_added;
        assert(-1 <= diff && diff <= 1);
    }



    // Actually, cut player gets H
// Actually Actually, sure it gets H but it just needs the matchings...
// TODO Ok so can we just call this with split_only and matchings of those?
    template<typename GG, typename M>
    Bisectionp cut_player(const GG &g, const vector<unique_ptr<M>> &given_matchings, double &h_multi_cond_out) {
        l.debug() << "Running Cut player" << endl;
        typename GG::template NodeMap<double> probs(g);
        vector<Node> all_nodes;

        //uniform_int_distribution<int> uniform_dist(0, 1);
        for (typename GG::NodeIt n(g); n != INVALID; ++n) {
            all_nodes.push_back(n);
        }
            uniform_int_distribution<int> uniform_dist(0, 1);
            for (typename GG::NodeIt n(g); n != INVALID; ++n) {
                probs[n] = uniform_dist(random_engine)
                       ? 1.0 / all_nodes.size()
                       : -1.0 / all_nodes.size();
        }

        size_t num_vertices = all_nodes.size();

        ListEdgeSet H(g);
        ListEdgeSet H_single(g);
        for (const unique_ptr<M> &m : given_matchings) {
            for (auto& e : *m) {
                Node u = e[0];
                Node v = e[1];
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
        shuffle(all_nodes.begin(), all_nodes.end(), random_engine);
        sort(all_nodes.begin(), all_nodes.end(), [&](Node a, Node b) {
            return probs[a] < probs[b];
        });

        size_t size = all_nodes.size();
        // With subdivisions, won't be this way longer
        //assert(size % 2 == 0);
        all_nodes.resize(size / 2);
        auto b = Bisectionp(new Bisection(all_nodes.begin(), all_nodes.end()));
        l.debug() << "Cut player gave the following cut: " << endl;
        print_cut(*b, l.debug());

        // So how does it give output?
        // Ok it assigns h_outs, but actually also returns Bisectionp
        auto hcs = CutStats<decltype(H)>(H, num_vertices, *b);
        l.progress() << "H conductance: " << hcs.conductance() << ", num cross: " << hcs.crossing_edges << endl;
        h_multi_cond_out = hcs.conductance();
        auto hscs = CutStats<decltype(H_single)>(H_single, num_vertices, *b);
        l.progress() << "H_single conductance: " << hscs.conductance() << ", num cross: " << hscs.crossing_edges << endl;

        return b;
    }

    // returns capacity that was required
// Maybe: make the binsearch an actual binsearch
// TODO Let listedgeset just be 2-arrays of nodes. Lemon is getting in the way too much.
// But also what is assigned in MtchResult?
    MatchResult matching_player(const set<Node> &bisection, Matching& m_out) {
        MatchingContext mg(gc.g);
        make_sink_source(mg.g, mg, bisection);

        unique_ptr<FlowAlgo> p;
        MatchResult mr = bin_search_flows(mg, p, gc.nodes.size()/2);

        decompose_paths(mg, p, m_out);

        // Now how do we extract the cut?
        // In this version, in one run of the matching the cut is strictly decided. We just need
        // to decide which one of them.
        // Only when we change to edge will the cut need to be explicitly extracted.
        // Rn the important thing is to save cuts between rounds so I can choose the best.

        return mr;
    }

    // returns capacity that was required
// Maybe: make the binsearch an actual binsearch
// TODO Let listedgeset just be 2-arrays of nodes. Lemon is getting in the way too much.
// But also what is assigned in MtchResult?
    MatchResult sub_matching_player(const set<Node> &bisection, vector<array<Node, 2>>& m_out) {
        MatchingContext mg(sgc.sub_g);
        make_sink_source(sgc.only_splits, mg, bisection);
        // TODO so have s, t been created on the big greaph?
        Node s = mg.s;
        int id = sgc.sub_g.id(s);
        cout << id << endl;
        cout << countNodes(sgc.sub_g) << endl;

        unique_ptr<FlowAlgo> p;
        MatchResult mr = bin_search_flows(mg, p, sgc.split_vertices.size()/2);

        decompose_paths(mg, p, m_out);

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
    // IS this right?
    long sub_volume_treshold() {
        //return config.volume_treshold_factor * sgc.origContext.nodes.size();
        if (config.h_ratio)
            return sgc.origContext.num_edges * config.h_ratio;

        return (config.volume_treshold_factor * double(sgc.origContext.num_edges) / (pow(log2(sgc.origContext.num_edges), 2)));
    }

    /*
    // Ok lets attack from here
    // Theres a lot of risk for problems with "is this a cut in the orig graph or in the splits?
    unique_ptr<RoundReport> one_round() {
        unique_ptr<RoundReport> report = make_unique<RoundReport>();

        // So this needs to be a bisection of splitnodes, I feel this could be very opaque.
        // We'd need a subgraph that is just the splitnodes
        Bisectionp bisection = cut_player(gc.g, matchings, report->multi_h_expansion);

        // Matching on splitnodes, but we need to also save the actual cut...
        Matchingp matchingp(new Matching());
        MatchResult mr = matching_player(*bisection, *matchingp);
        matchings.push_back(move(matchingp));

        //c.cuts.push_back(move(mr.cut_from_flow));
        report->index = sub_past_rounds.size();
        report->capacity_required_for_full_flow = mr.capacity;
        report->cut = move(mr.cut_from_flow);
        auto cs = CutStats<G>(gc.g, gc.nodes.size(), *report->cut);
        report->g_expansion = cs.expansion();
        l.progress() << "G cut expansion " << report->g_expansion << endl;
        report->volume = cs.minside_volume();
        l.progress() << "G cut minside volume " << cs.minside_volume() << endl;
        l.progress() << "G cut maxside volume " << cs.maxside_volume() << endl;
        report->relatively_balanced = report->volume > volume_treshold();
        return move(report);
    }
*/
    // Ok lets attack from here
    // Theres a lot of risk for problems with "is this a cut in the orig graph or in the splits?
    unique_ptr<RoundReport> sub_one_round() {
        unique_ptr<RoundReport> report = make_unique<RoundReport>();

        double h_multi_out_sub = 0;
        //Bisectionp sub_bisection = cut_player(sgc.only_splits, sub_matchings, h_multi_out_sub);
        Bisectionp sub_bisection = cut_player(sgc.only_splits, sub_matchings, report->multi_h_conductance);
        // Well ok, it's doing the first random thing well.
        // TODO test on rest...

        Matchingp smatchingp(new Matching());
        MatchResult smr = sub_matching_player(*sub_bisection, *smatchingp);
        sub_matchings.push_back(move(smatchingp));

        // TODO ocmputation of cut at the end is_ wrong...
        //c.cuts.push_back(move(mr.cut_from_flow));
        report->index = sub_past_rounds.size();
        report->capacity_required_for_full_flow = smr.capacity;
        report->cut = make_unique<Cut>();
        for(auto& n : *(smr.cut_from_flow)) {
            //if(sgc.n_cross_ref[n] != INVALID) {
                report->cut->insert(sgc.n_cross_ref[n]);
            //}
        }
        auto cs = CutStats<G>(sgc.origContext.g, sgc.origContext.nodes.size(), *report->cut);
        //report->g_expansion = cs.expansion();
        //l.progress() << "SUBG cut expansion " << report->g_expansion << endl;
        report->g_conductance = cs.conductance();
        if(report->g_conductance == 1) {
            cout << "LYING" << endl;
        }
        l.progress() << "SUBG cut conductance: " << report->g_conductance << endl;
        report->volume = cs.minside_volume();
        l.progress() << "SUBG cut minside volume " << cs.minside_volume() << endl;
        l.progress() << "SUBG cut maxside volume " << cs.maxside_volume() << endl;
        //Q: >, >=?
        report->relatively_balanced = report->volume >= sub_volume_treshold();
        cout << "Volume is: " << report->volume << " Threshold is: " << sub_volume_treshold() << endl;
        return move(report);
        // Thing is, the cut is not a "materialized cut" in the subdiv graph. But the stats we want are the implied
        // cut on the orig graph.
    }

    /*
    // Stopping condition
    bool should_stop() {
        int i = sub_past_rounds.size();
        if(i == 0) return false;
        if(i >= config.max_rounds && config.max_rounds != 0) return true;

        const auto& last_round = sub_past_rounds[sub_past_rounds.size() - 1];
        if(config.use_H_phi_target && last_round->multi_h_expansion >= config.H_phi_target) {
            cout << "H Expansion target reached, this will be case 1 or 3. According to theory, this means we probably won't find a better cut. That is, assuming you set H_phi right. "
                    "If was used together with G_phi target, this also certifies the input graph is a G_phi expander unless there was a very unbaanced cut somewhere, which we will proceed to look for." << endl;
            reached_H_target = true;
            return true;
        }

        if(config.use_G_phi_target)
        if(last_round->g_expansion >= config.G_phi_target) {
            if(config.use_volume_treshold && last_round->relatively_balanced) {
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
    }
     */

    // Stopping condition
    bool sub_should_stop() {
        int i = sub_past_rounds.size();
        if(i == 0) return false;
        if(i >= config.max_rounds && config.max_rounds != 0) return true;

        const auto& last_round = sub_past_rounds[sub_past_rounds.size() - 1];

        //if (config.use_volume_treshold && (last_round->relatively_balanced)) {
        //    cout << "balanced cut" << endl;
        //    return true;
        //}
        if (last_round->multi_h_conductance < config.H_phi_target) {
            cout << "H Conductance target reached, this will be case 1 or 3. According to theory, this means we probably won't find a better cut. That is, assuming you set H_phi right. "
                    "If was used together with G_phi target, this also certifies the input graph is a G_phi expander unless there was a very unbaanced cut somewhere, which we will proceed to look for." << endl;
            reached_H_target = true;
            return true;
        }


        if((*last_round->cut).size() > 0 && last_round->g_conductance < config.G_phi_target) {
            return true;
            /*if(last_round->relatively_balanced) {
                cout << "CASE2 G Expansion target reached with a cut that is relatively balanced. Cut-matching game has found a balanced cut as good as you wanted it."
                     << endl;
                return true;
            }
            */

        }


    return false;
    }

    void run() {
        while (!sub_should_stop()) {
            //sub_past_rounds.push_back(one_round());
            sub_past_rounds.push_back(sub_one_round());
            print_end_round_message(sub_past_rounds.size()-1);
        }
    }
};

// TODO Make cut always the smallest (maybe)
// TODO (In edge version) Implement breaking-logik for unbalance
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
             cxxopts::value<double>()->implicit_value("1"))
            ("f,file", "File to read graph from", cxxopts::value<std::string>())
            ("r,max-rounds", "Number of rounds after which to stop (0 for no limit)", cxxopts::value<long>()->default_value("25"))
            ("s,seed", "Use a seed for RNG (optionally set seed manually)",
             cxxopts::value<int>()->implicit_value("1337"))
            ("p,partition", "Partition file to compare with", cxxopts::value<std::string>())
            ("o,output", "Output computed cut into file. The cut is written as the vertices of one side of the cut.", cxxopts::value<std::string>())
            ("n,nodes", "Number of nodes in graph to generate. Should be even. Ignored if -f is set.",
             cxxopts::value<long>()->default_value("100"))
            ("h_factor", "factor of push relabel height",
             cxxopts::value<double>()->implicit_value("1"))
            ("h_ratio", "use balance ratio instead",
             cxxopts::value<double>()->implicit_value("0.0"))
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
        assert(!config.input.load_from_file);
        config.input.n_nodes_to_generate = result["nodes"].as<long>();
    if (result.count("max-rounds"))
        config.max_rounds = result["max-rounds"].as<long>();
    if (result.count("verbose"))
        l.verbose = result["verbose"].as<bool>();
    if (result.count("Silent"))
        l.silent = result["Silent"].as<bool>();

    if (result.count("seed")) {
        config.seed_randomness = true;
        config.seed = result["seed"].as<int>();
    }

    if (result.count("output")) {
        config.output_cut = true;
        config.output_file = result["output"].as<string>();
    }
    if (result.count("partition")) {
        config.compare_partition = true;
        config.partition_file = result["partition"].as<string>();
    }
    if (result.count("h_factor")) {
        config.h_factor = result["h_factor"].as<double>();
    }
    if (result.count("h_ratio")) {
        config.h_ratio = result["h_ratio"].as<double>();
    }
}





vector<list<ListDigraph::Node>> unit_flow(const ListGraph &ug, const ListDigraph &g, double h, ListDigraph::NodeMap<double> &sink_node_cap, ListDigraph::ArcMap<double> &cross_edge_source,
               ListDigraph::ArcMap<double> &flow, ListDigraph::NodeMap<double> &node_flow, ListDigraph::NodeMap<int> &degree,
               ListDigraph::ArcMap<double> &edge_cap, vector<list<ListDigraph::Node>> &level_queue, ListDigraph::NodeMap<int> &node_label, set<Node> A) {
    bool excess_flow = true;
    unit_start:
    while (excess_flow) {
        //cout << "Excess flow iter" << endl;
        excess_flow = false;
        for (int level_iter = 0; level_iter < h - 1; level_iter++) {
            for (auto list_it : level_queue[level_iter]) { //level_queue[level_iter].cbegin(); list_it != level_queue[level_iter].cend(); ++list_it) {
                if (A.count(ug.nodeFromId(g.id(list_it))) == 0)
                    continue;
                if (node_flow[list_it] > sink_node_cap[list_it]) {  //Push-relabel(v)
                    for (ListDigraph::OutArcIt e(g, list_it); e!=INVALID; ++e) {
                        //Q: graph adaptor
                        if (g.source(e) == g.target(e) || A.count(ug.nodeFromId(g.id(g.source(e)))) == 0 || A.count(ug.nodeFromId(g.id(g.target(e)))) == 0)
                            continue;
                        if (g.id(g.source(e)) >= g.id(g.target(e)))
                            continue;
                        if (node_label[g.target(e)] == level_iter - 1 && edge_cap[e] - flow[e] > 0) {

                            // push
                            double ex = node_flow[g.target(e)];
                            double rf = flow[e] - edge_cap[e];
                            double deg_minus_ex = degree[list_it] - ex;
                            double phi = min(ex, min(rf, deg_minus_ex));
                            flow[e] += phi;
                            flow[e] -= phi;                         
                            node_flow[list_it] -= phi;
                            node_flow[g.target(e)] += phi;
                            //don't relabel
                            //
                            excess_flow = true;
                        }
                        else {
                            //Relabel v += 1
                            node_label[list_it] += 1;
                            level_queue[level_iter].remove(list_it);
                            level_queue[level_iter + 1].push_back(list_it);

                            excess_flow = true;
                        }
                        goto unit_start;
                    }
                }
            }
        }
    }
    return level_queue;
}

using DG = ListDigraph;
using DGNode = typename DG::Node;
template<class T> using DGNodeMap = typename DG::template NodeMap<T>;
using DGNodeIt = typename DG::NodeIt;
using Arc = typename DG::Arc;
template<class T> using ArcMap = typename DG::template ArcMap<T>;
using DGOutArcIt = typename DG::OutArcIt;


ListDigraph *digraph_from_graph(G &g, DG &dg) {

    for(NodeIt n(g); n!=INVALID; ++n)
        dg.addNode();

    for(EdgeIt a(g); a!=INVALID; ++a) {
        Arc a1 = dg.addArc(dg.nodeFromId(g.id(g.u(a))), dg.nodeFromId(g.id(g.v(a))));
        Arc a2 = dg.addArc(dg.nodeFromId(g.id(g.v(a))), dg.nodeFromId(g.id(g.u(a))));

    }

    return &dg;
}


ListDigraph *digraph_from_graph(G &g, DG &dg, ArcMap<Arc>& reverse_arc) {

    for(NodeIt n(g); n!=INVALID; ++n)
        dg.addNode();

    for(EdgeIt a(g); a!=INVALID; ++a) {
        Arc a1 = dg.addArc(dg.nodeFromId(g.id(g.u(a))), dg.nodeFromId(g.id(g.v(a))));
        Arc a2 = dg.addArc(dg.nodeFromId(g.id(g.v(a))), dg.nodeFromId(g.id(g.u(a))));
        reverse_arc[a1] = a2;
        reverse_arc[a2] = a1;
    }

    return &dg;
}

struct flow_instance {

    flow_instance (DG& dg_, double phi) :
    edge_flow(dg_, 0.0),
    edge_cap(dg_, 2.0/phi),
    reverse_arc(dg_),
    node_flow(dg_, 0.0),
    node_cap(dg_, 0.0),
    node_label(dg_, 0.0)
    {} ;

    int h; 
    double phi;
    int n;
    int e;

    ArcMap<double> edge_flow;
    ArcMap<double> edge_cap;
    ArcMap<Arc> reverse_arc;

    DGNodeMap<double> node_flow;
    DGNodeMap<double> node_cap;

    DGNodeMap<int> node_label;

    set<DGNode> A;
    set<DGNode> R;
    list<Arc> arc_nodes;
};

int OutDegree(DG& dg, DGNode n) {
    int s = 0;
    for(DGOutArcIt e(dg, n);  e != INVALID; ++e) {
        s += 1;
    }
    return s;
}

//Q: should iterate over edges in cut
set<DGNode> level_cut(DG& dg, flow_instance& fp, vector<list<DGNode>>& level_queue, set<DGNode>& set_A, set<DGNode>& set_R) {
    int n_cut = set_A.size();
    int cut_index = 0;
    int cut_sum = 0;
    int s_vol;
    int z_i;
    set<DGNode> R;
    int e = fp.e;
    int n_upper_nodes;

    for (int i = level_queue.size() - 1 ; i >= 0; i--) {
        n_upper_nodes = 0;
        s_vol = 0;
        z_i   = 0;
        if (level_queue[i].size() > 0)
            cout << "local flow: level queue at level: " << i << " has size: " << level_queue[i].size() << endl;
        int r_count = 0;
        for (auto& n : set_R)
            if (find(level_queue[i].begin(), level_queue[i].end(), n) != level_queue[i].end())
                r_count += 1;
        if (r_count)
            cout << "local flow: r count at lvl: " << i << " is: " << r_count << endl;
        for (auto& n: level_queue[i]) {
            n_upper_nodes++;
            for (DGOutArcIt e(dg, e); e!= INVALID; ++e) {
                s_vol++;
                if (fp.node_label[n] - 1 == fp.node_label[dg.target(e)]); {
                    z_i++;
                }
            }
        }
        if (z_i < 5 * s_vol * log2(e) / fp.h) {
            cut_index = i;
            break;
        }
    }
    assert (cut_index >= 0);
    fp.A.clear();
    R.clear();
    if (n_upper_nodes < set_A.size()/2) {
        for (int i = level_queue.size() - 1; i >= cut_index; i--) {
            for (auto& n: level_queue[i])
                R.insert(n);
            level_queue[i].clear();
        }
    }
    else {
        for (int i = cut_index - 1; i >= 0; i--) {
            level_queue[i].clear();
            for (auto& n: level_queue[i])
                R.insert(n);

        }
    }
    for (int i = level_queue.size() - 1; i >= 0; i--) {
        for (auto& n: level_queue[i]) {
            if (R.count(n) == 0)
                fp.A.insert(n);
        }
    }

    return R;
}

void adjust_flow_source (DG& dg, flow_instance& fp, set<DGNode> &set_A, set<DGNode> &set_R) {
    for (auto& n: set_R) {
        for(DGOutArcIt e(dg, n); e != INVALID; ++e) {
            if (!set_R.count(dg.target(e))) {
                fp.node_flow[n] += 2/fp.phi;
                fp.edge_cap[e] = 2/fp.phi;
            }
        }
    }
}

void uf(DG& dg, flow_instance& fp) {

    //Set up level queues
    vector<list<DGNode>> level_queue;
    for (int i = 0; i < fp.h; i++) {
        level_queue.push_back(list<DGNode>());
    }

    unit_setup:
    for (int i = 0; i < fp.h; i++) {
        level_queue[i].clear();
    }

    for (DGNodeIt n(dg); n != INVALID; ++n)
        level_queue[0].push_back(n);

    bool excess_flow = true; 

    struct push_relabel {

        struct push {

        };

        struct relabel {

        };
    };


    excess_flow = true;
    cout << "local flow: start unit flow" << endl;
    unit_start:

    while (excess_flow) {
        excess_flow = false;
        for (int lv = 0; lv < fp.h - 1; lv++) {
            for (auto& n : level_queue[lv]) {
                //cout << "local flow: node flow: " << fp.node_flow[n] << " node cap " << fp.node_cap[n] << endl;
                if (fp.node_flow[n] > fp.node_cap[n]) { //push-relabel
                    //cout << "local flow: push relabel" << endl;
                    for (DGOutArcIt e(dg, n); e != INVALID; ++e) {

                        if (dg.source(e) == dg.target(e))
                            continue;
                        if (!fp.A.count(dg.source(e)) || !fp.A.count(dg.target(e)))
                            //cout << "local flow: try to push inside R" << endl;
                            continue;

                        if (fp.node_label[n] - fp.node_label[(dg.target(e))] == 1 && fp.edge_cap[e] - fp.edge_flow[e] > 0) {// push 
                            //assert(fp.node_flow[dg.target(e)] - fp.node_cap[dg.target(e)] == 0);
                            double ex_flow = fp.node_flow[n] - fp.node_cap[n];
                            double res_flow = fp.node_cap[n] - fp.node_flow[n];
                            double deg_min_ex = fp.node_cap[n] * fp.phi/2.0 - (fp.node_cap[n] - fp.node_flow[n]) ;
                            double phi = min(ex_flow, min(res_flow, deg_min_ex));
                            fp.node_flow[n] -= phi;
                            fp.node_flow[dg.target(e)] += phi;
                            assert (n != dg.target(e));
                            //fp.node_flow[dg.source(e)] -= phi;
                            fp.edge_flow[e] += phi;
                            fp.edge_flow[fp.reverse_arc[e]] -= phi;
                            excess_flow = true;
                            cout << "local flow: " << fp.node_flow[n] << " " << fp.node_cap[n] << endl;
                            cout << "local flow:" << ex_flow << " " << res_flow << " " << deg_min_ex << endl;
                            cout << "local flow: Pushed " << phi << " from " << dg.id(n) << " to " << dg.id(dg.target(e)) << " with cap " << fp.node_cap[dg.target(e)] << endl;
                            goto unit_start;
                        }
                    }
                    // relabel
                    for (DGOutArcIt e(dg, n); e != INVALID; ++e)
                        if (fp.edge_cap[e] - fp.edge_flow[e] > 0)
                            assert (fp.node_label[n] <= fp.node_label[dg.target(e)] );
                    cout << "local flow: relabel" << endl;
                    level_queue[lv + 1].push_back(n);
                    fp.node_label[n] = fp.node_label[n] + 1;
                    level_queue[lv].remove(n);
                    excess_flow = true;
                    goto unit_start;
                }   
            }
        }
    }
    cout << "finish run of uf" << endl;
    int cut_size_before = fp.A.size();
    cout << "cut size before: " << cut_size_before << endl;
    cout << "complement size before: " << fp.R.size() << endl;
    set<DGNode> R = level_cut(dg, fp, level_queue, fp.A, fp.R);
    adjust_flow_source(dg, fp, fp.A, fp.R);
    //NOT QUITE RIGHT
    for (auto& n: fp.R)
        fp.A.erase(n);
    cout << "cut_size_after" << fp.A.size() << endl;
    cout << "complement siz after" << fp.R.size() << endl;
    //assert (fp.A.size() <= cut_size_before);

    if (cut_size_before == fp.A.size())
        return;
    goto unit_setup;
    //End
}

set<Node> slow_trimming(GraphContext& gc, Configuration conf, set<Node> cut, double phi) {
    DG dg;
    G sg;
    G split_graph;

    struct split_node {
        DGNode v1;
        DGNode v2;
    };

    DGNodeMap<Node> dg_to_ug(dg);
    NodeMap<DGNode> ug_to_dg(gc.g);
    NodeMap<DGNode> split_to_ug(gc.g);
    NodeMap<split>  ug_to_split(gc.g);
    map<split_node, Node> split_to_ug;
    ListDigraph::ArcMap cap(dg, 0);
    NodeMap<Node> degree(gc.g, 0);
    list<split> split_nodes;

    NodeMap<Node> sg_to_orig(sg);

    NodeMap<bool> in_cut(gc.g, false);
    for (auto& n: cut) {
        in_cut[n] = true;
    }

    for (ArcIt e(gc.g); e != INVALID; ++e) {
        degree[gc.g.u(e)] += 1;
        degree[gc.g.v(e)] += 1;
    } 

    for (NodeIt n(gc.g); n != INVALID; ++n) {
        if (!in_cut[n]) {
        Node sn_1 = split_graph.addNode();
        Node sn_2 = split_graph.addNode();
        sg_to_orig(sn_1) = n;
        sg_to_orig(sn_2) = n;

        DGNode dn_1 = dg.addNode();
        dg_to_ug[dn_1] = n;
        DGNode dn_2 = dg.addNode();
        dg_to_ug[dn_2] = n;
        split sp;
        sp.v1 = dn_1;
        sp.v2 = dn_2;
        split_to_ug[split] = n;
        split_nodes.insert(sp);
        ug_to_split[n] = sp;
        }
    }

    //Add 2 arc between split nodes and set cap to degree
    for (NodeIt n(gc.g); n != INVALID; ++n) {
        split sg = ug_to_split(n);
        Arc a1 = dg.addArc(sg.v1, sg.v2);
        Arc a2 = dg.addArc(sg.v2, sg.v1);
        cap[a] = degree[split_to_ug];
    }

    //Add other arcs
    for (ArcIt e(gc.g); e != INVALID; ++e) {
        
    }

    //Added split nodes and capacity between them
    //Need filter later
    DGNode s = dg.addNode();
    DGNode t = dg.addNode();
    ListDigraph::ArcMap<int> cap(dg);
    ListDigraph::ArcMap<int> node_cap(dg);
    for (NodeIt n(dg); n != INVALID; ++n) {
        if (n == s || n == t || in_cut[n])
            continue;
        if (!in_cut[gc.g.nodeFromId(dg.id(n))]) {
            Arc e = dg.addArc(n, t);
            cap[e] = 2/phi;
        }
    }

    for (EdgeIt e(gc.g); e != INVALID; ++e) {
        int id_u = gc.g.id(gc.g.u(e));
        int id_v = gc.g.id(gc.g.v(e));
        if (in_cut[gc.g.u(e)] && in_cut[gc.g.v(e)]) {
            Arc a = dg.addArc(dg.nodeFromId(id_u), dg.nodeFromId(id_v));
            cap[a] = 0;
        }
        else if (in_cut[gc.g.u(e)] && !in_cut[gc.g.v(e)]) {
            Arc a = dg.addArc(s, dg.nodeFromId(id_u));
            cap[a] = 2/phi;
        }
        else if (!in_cut[gc.g.u(e)] && in_cut[gc.g.v(e)]) {
            Arc a = dg.addArc(dg.nodeFromId(id_u), s);
            cap[a] = 2/phi;
        }
        else {
            Arc a1 = dg.addArc(dg.nodeFromId(id_u), dg.nodeFromId(id_v));
            Arc a2 = dg.addArc(dg.nodeFromId(id_v), dg.nodeFromId(id_u));
            cap[a1] = 2/phi;
            cap[a2] = 2/phi;
        }
    }
    //sorted descending
    /*
    int it = 0;
    for (auto& n: cut) {
        dg.removeNode(dg.nodeFromId(gc.g.id(n) -it));
        it--
    }
    */


    Preflow<DG> preflow(dg, cap, s, t);
    preflow.run();
    cout << "local flow: cut size before: " << cut.size() << endl;
  

    int sz = 0;
    cut.clear();
    for (DGNodeIt n(dg); n != INVALID; ++n)
        if (preflow.minCut(n) && n != s && n != t)
            cut.insert(gc.g.nodeFromId(dg.id(n)));
    cout << "local flow: cut size after " << cut.size() << endl;

    return cut;

}

set<Node> trimming(GraphContext& gc, Configuration conf, set<Node> cut, double phi) {
    //Working on undirected graph
    //"Forward direction" is higher node ID to lower node ID
    //Delta
    //T
    //c
    //
    //f(v) <= T(v) - flow conditions
    //f(v) > T(V) - excess flow
    //f_1 (u, v) = 0
    //l1(u) = 0
    //|delta< < 3m/2
    //int h = 40 * log2(gc.num_edges) / phi;
    //EdgeMap<double> flow;

    assert (phi >= 0.00001);
    DG dg;
    digraph_from_graph(gc.g, dg);

    flow_instance fp = flow_instance(dg, phi);
    fp.n = gc.nodes.size();
    fp.e = gc.num_edges;
    set<DGNode> R;

    for (auto& n: cut)
        R.insert(dg.nodeFromId(gc.g.id(n)));
    set<DGNode> temp_all_nodes;
    
    for (int i = 0; i < gc.nodes.size(); ++i)
        temp_all_nodes.insert(dg.nodeFromId(i));

    //Q: this right?
    std::set_difference(temp_all_nodes.begin(), temp_all_nodes.end(), R.begin(), R.end(),
                        std::inserter(fp.A, fp.A.end()));
                        R.swap(fp.A);

    fp.h = 40 * log2(gc.num_edges) /phi;
    fp.phi = phi;
    //Wasteful but still mlogm
    //Crossing edge sources
    bool added_source = false;
    for (auto& n: R) {
        for (DGOutArcIt e(dg, n); e != INVALID; ++e) {
            if (R.count(dg.source(e)) && !R.count(dg.target(e))) {
                //fp.node_flow[dg.source(e)] += 2./phi;
                fp.node_flow[dg.target(e)] += 2.0/phi;
                added_source = true;
            }
            else if (!R.count(dg.source(e)) && R.count(dg.target(e))) {
                fp.node_flow[dg.target(e)] += 2./phi;
                //fp.node_flow[dg.source(e)] += 2./phi;
                added_source = true;
           }
        }
        fp.node_cap[n] = 0.0;
        fp.node_label[n] = 0;
        fp.node_flow[n] = 0.0;
    }
    assert (added_source);
    //set sink capacities
    //Q: equals degree?
    for (auto& n : fp.A) {
        fp.node_cap[n] = 0.0;
        fp.node_flow[n] = 0.0;
        assert (R.count(n) == 0);
        for (DGOutArcIt e(dg, n); e != INVALID; ++e)
            if (!R.count(dg.target(e)) && !R.count(dg.source(e))) {
                fp.node_cap[n] += 1;
                fp.edge_cap[e] = 2.0/phi;
            }
            else
                fp.edge_cap[e] = 0;
        fp.node_label[n] = 0;
        fp.node_flow[n] = 0.0;
        assert(fp.node_cap[n] >= 0.0);

    }
    //for (ListDigraph::ArcIt e(DG); e != INVALID; ++e) {
    //    fp.edge_cap[e] = 2/phi;
    //}
    assert (R.size() > 0);
    for (auto& n : R) {
        fp.node_flow[n] = 0.0;
        for (DGOutArcIt e(dg, n); e != INVALID; ++e) {
            if (!R.count(dg.target(e))) {
                fp.edge_cap[e] = 2.0/phi;
                fp.edge_flow[e] = 2.0/phi;
                fp.node_flow[dg.target(e)] += 2.0/phi;
                fp.edge_flow[fp.reverse_arc[e]] = -2.0/phi;
            }
            else {
                fp.edge_cap[e] = 0;
                fp.edge_flow[e] = 0.0;
            }
        }
        fp.node_cap[n] = 0.0;
    }
 
    // add edge nodes 

    for(DGNodeIt n(dg); n != INVALID; ++n) {
        cout << "local flow: node flow : " << fp.node_flow[n] << endl;
        for(DGOutArcIt e(dg, n); e != INVALID; ++e) {
            ;
        }
    }
    return cut;

    fp.R = R;
    uf(dg, fp);

    //dummy
    cut.clear();
    for (auto& n: fp.A) {
        cut.insert(gc.g.nodeFromId(dg.id(n)));
    }
    return cut;
}


void graph_from_cut(GraphContext &g, GraphContext &sg, set<Node> cut) {

    map<Node, Node> reverse_map = map<Node, Node>();
    set<Node> all_nodes = set<Node>();
    set<Node> complement_nodes = set<Node>();
    sg.num_edges = 0;
    assert (sg.nodes.size() == 0);

    for (auto n : cut) {
        Node x = sg.g.addNode();
        sg.nodes.push_back(x);
        //Maybe not necessary
        reverse_map[n] = x;
        sg.orig_degree[x] = g.orig_degree[n];
    }


    int sum_all_edges = 0;
    for (const auto &n : cut) {
        for (IncEdgeIt a(g.g, n); a!=INVALID; ++a) {
            if (cut.count(g.g.target(a)) > 0 && cut.count(g.g.source(a)) > 0)
                sum_all_edges++;
            if (cut.count(g.g.target(a)) > 0 && cut.count(g.g.source(a)) > 0  && g.g.source(a) < g.g.target(a)) {//findEdge(sg.g, reverse_map[g.g.source(a)], reverse_map[g.g.target(a)]) == INVALID) { //Edge inside cut
                assert (reverse_map[n] != reverse_map[g.g.target(a)]); // no self -loop
                assert (sg.g.id(reverse_map[g.g.source(a)]) < sg.nodes.size() && sg.g.id(reverse_map[g.g.target(a)]) < sg.nodes.size());
                sg.g.addEdge(reverse_map[g.g.source(a)], reverse_map[g.g.target(a)]);
                sg.num_edges++;
            }
            //Add self-oops ?
            else if (cut.count(g.g.target(a)) == 0 && cut.count(g.g.source(a)) > 0 && g.g.source(a) < g.g.target(a)) {//&& findEdge(sg.g, reverse_map[g.g.source(a)], reverse_map[g.g.target(a)]) == INVALID) { 
                sg.g.addEdge(reverse_map[g.g.source(a)], reverse_map[g.g.source(a)]);
                sg.num_edges++;
            }
    }   }
    return;
} 

map<Node, Node> graph_from_cut(GraphContext &g, GraphContext &sg, set<Node> cut, map<Node, Node> old_map, bool complement=false) {
    map<Node, Node> new_map = map<Node, Node>();
    map<Node, Node> reverse_map = map<Node, Node>();
    set<Node> all_nodes = set<Node>();
    set<Node> complement_nodes = set<Node>();
    sg.num_edges = 0;
    assert (sg.nodes.size() == 0);
    
    if (complement == true) {
        for (NodeIt n(g.g); n!=INVALID; ++n) {
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
        sg.orig_degree[x] = g.orig_degree[n];
    }
    //sort(sg.nodes.begin(), sg.nodes.end());

    int sum_all_edges = 0;
    for (const auto &n : cut) {
        for (IncEdgeIt a(g.g, n); a!=INVALID; ++a) {
            if (cut.count(g.g.target(a)) > 0 && cut.count(g.g.source(a)) > 0)
                sum_all_edges++;
            if (cut.count(g.g.target(a)) > 0 && cut.count(g.g.source(a)) > 0  && g.g.source(a) < g.g.target(a)) {//findEdge(sg.g, reverse_map[g.g.source(a)], reverse_map[g.g.target(a)]) == INVALID) { //Edge inside cut
                assert (reverse_map[n] != reverse_map[g.g.target(a)]); // no self -loop
                assert (sg.g.id(reverse_map[g.g.source(a)]) < sg.nodes.size() && sg.g.id(reverse_map[g.g.target(a)]) < sg.nodes.size());
                sg.g.addEdge(reverse_map[g.g.source(a)], reverse_map[g.g.target(a)]);
                sg.num_edges++;
            }
            //Add self-oops ?
            else if (cut.count(g.g.target(a)) == 0 && cut.count(g.g.source(a)) > 0 && g.g.source(a) < g.g.target(a)) {//&& findEdge(sg.g, reverse_map[g.g.source(a)], reverse_map[g.g.target(a)]) == INVALID) { 
                sg.g.addEdge(reverse_map[g.g.source(a)], reverse_map[g.g.source(a)]);
                sg.num_edges++;
            }
    }   }
    cout << "after decomp on cut with e: " << sum_all_edges << " retains: " << sg.num_edges << endl;
    //assert (sum_all_edges / 2 == sg.num_edges);
    return new_map;
}


vector<set<Node>> find_connected_components(GraphContext &g) {

    NodeMap<bool> visited_nodes(g.g, false);
    vector<set<Node>> labels;

    Bfs<ListGraph> bfs(g.g);
    bfs.init();

    //bfs.init();
    //bfs.start();
    
    int n_visited = 0;
    int cc = 0;
    Node source;
    Node y;

    int test_check = 0;
    for (NodeIt n(g.g); n != INVALID; ++n)
        test_check = test_check + 1;
    assert (test_check == g.nodes.size());
    while (n_visited < g.nodes.size()) {
        labels.push_back(set<Node>());

        for(NodeIt n(g.g); n != INVALID; ++n) {
            //cout << "Checking node n: " << g.g.id(n) << endl;
            if (visited_nodes[n] == false) {
                y = n;

                break;
            }
            //assert (false);
        }

        cout << "Choosing node: " << g.g.id(y) << endl;
        bfs.addSource(y);
        //bfs.run();
        assert (y != INVALID);
        assert (visited_nodes[y] == false);

        if (bfs.emptyQueue()) {
            cout << "Unreachable ?" << endl;
            labels[cc].insert(y);
            visited_nodes[y] = true;
            n_visited++;
            cc++;
            continue;
        }
        assert (y != INVALID);
        //else
        //    bfs.processNextNode();
        //visited_nodes[source] = true;
        //labels[cc].insert(source);
        //n_visited++;

        while (!bfs.emptyQueue() && y != INVALID) {
            //cout << "working on node: " << g.g.id(y) << endl;
            if (!visited_nodes[y]) {
                //y = bfs.nextNode();
                //assert (y != source);
                labels[cc].insert(y);
                visited_nodes[y] = true;
                n_visited++;
            }
            y = bfs.processNextNode();
            //assert(visited_nodes[y] == false); 
        }
        assert (labels[cc].size() > 0);
        cc++;
    }
    int tot = 0;
    for (auto &l : labels)
        tot = tot + l.size();
    cout << "N visited " << n_visited << " g node size " << g.nodes.size() << " cc:  " << cc << endl;
    assert (n_visited == g.nodes.size());
    assert (cc <= g.nodes.size());
    assert (tot == g.nodes.size());
    return labels;
}


/*
set<Node> cut_from_cm(GraphContext& gc, Configuration config) {
    cout << "init cut-matching" << endl;
    default_random_engine random_engine = config.seed_randomness
                    ? default_random_engine(config.seed)
                    : default_random_engine(random_device()());
    CutMatching cm(gc, config, random_engine);
    cout << "Start cut-matching" << endl;
    cm.run();
    cout << "Finish cut-matching" << endl;
    assert(!cm.sub_past_rounds.empty());
    auto& best_round = *max_element(cm.sub_past_rounds.begin(), cm.sub_past_rounds.end(), [](auto &a, auto &b) {
        return a->g_conductance < b->g_conductance;
    });

    return *(best_round->cut);
}
*/


double standalone_conductance(GraphContext& gc, set<Node> cut) {
    int e = gc.num_edges;
    int edges_interior = 0;
    int cross_edges = 0;
    int complement_edges = 0;
    for (G::ArcIt e(gc.g); e != INVALID; ++e) {
        if (cut.count(gc.g.source(e)) && cut.count(gc.g.target(e)))
            edges_interior++;
        else if ((cut.count(gc.g.source(e)) && !cut.count(gc.g.target(e))) || (!cut.count(gc.g.source(e)) && cut.count(gc.g.target(e))))
            cross_edges++;
        else
            complement_edges++;
    }
    cout << "local flow: interior e: " << edges_interior << " cross: " << cross_edges << " comp: " << complement_edges << endl;
    cout << "local flow: conductance: " << (1.0 * cross_edges)/min(edges_interior, complement_edges) << endl;
    return (1.0 * cross_edges) / min(edges_interior, complement_edges);
}

vector<map<Node, Node>> decomp(GraphContext &gc, ListDigraph &dg, Configuration config, map<Node, Node> map_to_original_graph, vector<set<Node>> cuts, vector<map<Node, Node>> node_maps_to_original_graph) {

    int x = 0;
    
    
    if (gc.nodes.size() == 0)
        return node_maps_to_original_graph;

    if (gc.nodes.size() == 1) {
        node_maps_to_original_graph.push_back(map_to_original_graph);
        return node_maps_to_original_graph;
    }

    if (!(connected(gc.g))) {
        vector<set<Node>> labels = find_connected_components(gc);
        int node_cnt = 0; 
        for (auto& sg_cut : labels) {
            cout << "decomp on component: n: " << sg_cut.size() << endl;
            for (auto& n : sg_cut)
                cout << gc.g.id(map_to_original_graph[n]) << " ";
            cout << endl;
            GraphContext sg;
            map<Node, Node> comp_map = graph_from_cut(gc, sg, sg_cut, map_to_original_graph);
            vector<map<Node, Node>> decomp_map;
            vector<map<Node, Node>> empty_map;
            decomp_map = decomp(sg, dg, config, comp_map, cuts, empty_map);
            //~sg.g();
            node_maps_to_original_graph.insert(node_maps_to_original_graph.end(), decomp_map.begin(), decomp_map.end());
            node_cnt = node_cnt + sg.nodes.size();
        }
        return node_maps_to_original_graph;
    }

    assert (connected(gc.g));

    //Q: check expansion
    if (gc.nodes.size() == 2) {
        map<Node, Node> map_1 = {{gc.g.nodeFromId(0), map_to_original_graph[gc.g.nodeFromId(0)]}};
        map<Node, Node> map_2 = {{gc.g.nodeFromId(1), map_to_original_graph[gc.g.nodeFromId(1)]}};
        node_maps_to_original_graph.push_back(map_1);
        node_maps_to_original_graph.push_back(map_2);
        return node_maps_to_original_graph;
    }
 
    //cout << "con-check, n: " << gc.nodes.size() << " e: " << gc.num_edges << endl;

    Node temp_node;
    Edge temp_edge;
    bool added_node = false;
    if (gc.nodes.size() % 2 != 0) {
        added_node = true;
        temp_node = gc.g.addNode();
        temp_edge = gc.g.addEdge(gc.nodes[gc.nodes.size() - 2], temp_node);
        gc.nodes.push_back(temp_node);
        gc.num_edges++;
    }


    //for (EdgeIt e(gc.g); e != INVALID; ++e) {
    //    assert (gc.g.u(e) != gc.g.v(e));
    //
    

    cout << "init cut-matching" << endl;
    
    default_random_engine random_engine = config.seed_randomness
                    ? default_random_engine(config.seed)
                    : default_random_engine(random_device()());
    CutMatching cm(gc, config, random_engine);
    cout << "Start cut-matching" << endl;
    cm.run();
    cout << "Finish cut-matching" << endl;
    assert(!cm.sub_past_rounds.empty());
    auto& best_round = *min_element(cm.sub_past_rounds.begin(), cm.sub_past_rounds.end(), [](auto &a, auto &b) {
        return a->g_conductance < b->g_conductance;
    });
    //Q: hack
    auto& last_round = *min_element(cm.sub_past_rounds.end() - 1, cm.sub_past_rounds.end(), [](auto &a, auto &b) {
        return a->g_conductance == b->g_conductance;
    });
    
    if (added_node) {
        (*(best_round->cut)).erase(temp_node);
        (*(last_round->cut)).erase(temp_node);
        gc.g.erase(temp_edge);
        gc.g.erase(temp_node);
        gc.nodes.pop_back();
        gc.num_edges--;
    }
    
    cout << "The best with highest expansion was found on round" << best_round->index << endl;
    cout << "Best cut sparsity: " << endl;
    auto &best_cut = best_round->cut;
    CutStats<G>(gc.g, gc.nodes.size(), *best_cut).print();

    set<Node> full;
    set<Node> cut_complement;

    for (int i = 0; i < gc.nodes.size() ; i++) {
       full.insert(gc.g.nodeFromId(i));   
    }
    //Cut on small side
    if ((*(last_round->cut)).size() < gc.nodes.size()/2) {
           set_difference(full.begin(), full.end(), (*(last_round->cut)).begin(), (*(last_round->cut)).end(),
           inserter(cut_complement, cut_complement.begin()));
           (*(last_round->cut)) = cut_complement;
           set_difference(full.begin(), full.end(), (*(best_round->cut)).begin(), (*(best_round->cut)).end(),
           inserter(cut_complement, cut_complement.begin()));
           (*(best_round->cut)) = cut_complement;

    }

    //unique_ptr<RoundReport> last_round = cm.sub_past_rounds[cm.sub_past_rounds.size() - 1];
    /*if (((*last_round->cut).size() == gc.nodes.size() || (*last_round->cut).size() == 0) && cm.reached_H_target) {
        cout << "CASE1 NO Goodenough cut (at all), G certified expander." << endl;
        node_maps_to_original_graph.push_back(map_to_original_graph);
    }*/
    
    cout << "local flow: " << "reached target ? " << cm.reached_H_target << " best conductance ? " << best_round->g_conductance << endl;
    cout << "local flow: " << "last conductance ?  " << last_round->g_conductance << " last size ? " << (*(last_round->cut)).size() << endl;
    cout << "local flow: " << "best size? " << (*(best_round->cut)).size() << endl;
    
    if ((*(best_round->cut)).size() == 0 || (*(last_round->cut)).size() == 0 || (best_round->g_conductance >= config.G_phi_target && cm.reached_H_target)) {
        cout << "CASE1 NO Goodenough cut (timeout), G certified expander." << endl;
        node_maps_to_original_graph.push_back(map_to_original_graph);
    }

    //break early due to balanced and good cut
    else if (best_round->g_conductance < config.G_phi_target && best_round->relatively_balanced) {
        assert ((*(best_round->cut)).size() > 0 != gc.nodes.size());
        cout << "CASE2 Goodenough balanced cut" << endl;
        GraphContext A;
        cout << "Create map to original graph" << endl;
        map<Node, Node> new_map = graph_from_cut(gc, A, *(last_round->cut), map_to_original_graph);
        assert (A.nodes.size() == (*(best_round->cut)).size());
        cout << "Decomp on A" << endl;

        vector<map<Node, Node>> empty_map;
        vector<map<Node, Node>> decomp_map = decomp(A, dg, config, new_map, cuts, empty_map);
        node_maps_to_original_graph.insert(node_maps_to_original_graph.end(), decomp_map.begin(), decomp_map.end());

        GraphContext R;
        cout << "(R) create map to original graph" << endl;
        new_map = graph_from_cut(gc, R, *(best_round->cut), map_to_original_graph, true);
        cout << "A nodes size: " << A.nodes.size() << " R nodes size: " << R.nodes.size() << " orig size " << gc.nodes.size() << endl;
        //Q:
        //assert (A.nodes.size() + R.nodes.size() == gc.nodes.size());
        vector<map<Node, Node>> empty_map_;
        vector<map<Node, Node>> decomp_map_ = decomp(R, dg, config, new_map, cuts, empty_map_);
        node_maps_to_original_graph.insert(node_maps_to_original_graph.end(), decomp_map_.begin(), decomp_map_.end());
    }

    //check best cut found so far
    else if (!(best_round->relatively_balanced) && best_round->g_conductance < config.G_phi_target) {  // last_round->g_conductance < config.G_phi_target && !(last_round->relatively_balanced)) {
        //assert (cm.reached_H_target);
        ListDigraph dg_;
        digraph_from_graph(gc.g, dg_);
        assert (((*(best_round->cut)).size()) != 0);

        cout << "Call local flow with cut of size: " << (*(best_round->cut)).size() << endl;
        standalone_conductance(gc, (*(best_round->cut)));
        *(best_round->cut) = slow_trimming(gc, config, *(best_round->cut), config.G_phi_target);
        cout << "After local flow, cut is reduced to n nodes: " << (*(best_round->cut)).size() << endl;
        standalone_conductance(gc, (*(best_round->cut)));
        assert (((*(best_round->cut)).size()) != 0);
        GraphContext V_over_A;
        GraphContext A;
        map<Node, Node> R_map = graph_from_cut(gc, V_over_A, (*best_round->cut), map_to_original_graph, true);
        map<Node, Node> A_map = graph_from_cut(gc, A, (*best_round->cut), map_to_original_graph, false);
        //Q: should hold? Why is this off by one?
        //assert (A.nodes.size() + V_over_A.nodes.size() == gc.nodes.size());
        //assert (V_over_A.nodes.size() > 0);
        node_maps_to_original_graph.push_back(A_map);
        vector<map<Node, Node>> empty_map;
        vector<map<Node, Node>> cuts_empty_map;
        vector<map<Node, Node>> decomp_map = decomp(V_over_A, dg, config, R_map, cuts, cuts_empty_map);
        node_maps_to_original_graph.insert(node_maps_to_original_graph.end(), decomp_map.begin(), decomp_map.end());
    }

    else { //provisional round limit
        cout << "CASE(4) no good cut, round break, G certified nothing." << endl;
        node_maps_to_original_graph.push_back(map_to_original_graph);
        assert (false);
    }

    return node_maps_to_original_graph;
}


int main(int argc, char **argv) {

    Configuration config = Configuration();
    parse_options(argc, argv, config);

    if(config.show_help_and_exit) return 0;

    GraphContext gc;
    initGraph(gc, config.input);
    ListDigraph dg;
    digraph_from_graph(gc.g, dg);

    cout << "n: gc.g.nodes.size()" << " e: " << gc.num_edges << endl;
    map<Node, Node> map_to_original_graph;
    for (NodeIt n(gc.g); n!=INVALID; ++n)
        map_to_original_graph[n] = n;

    vector<set<Node>> cuts = vector<set<Node>>();
    vector<map<Node, Node>> node_maps_to_original_graph = vector<map<Node, Node>>();

    map<Node, int> degree;
    for (NodeIt n(gc.g); n != INVALID; ++n) {
        int d = 0;
        for (IncEdgeIt e(gc.g, n); e != INVALID; ++e)
            d++;
        degree[n] = d;
    }

    //main
    vector<map<Node, Node>> cut_maps = decomp(gc, dg, config, map_to_original_graph, cuts, node_maps_to_original_graph);

    cout << "Done decomp" << endl;

    vector<int> all_nodes;

    int n_singletons = 0;
    vector<vector<Node>> cuts_node_vector;
    for (const auto &m : cut_maps) {
        if (m.size() == 1) {
            for (const auto &c : m)
                all_nodes.push_back(gc.g.id(c.second));
            n_singletons++;
            continue;
        }
        cuts_node_vector.push_back(vector<Node>());
        for (const auto &c : m) {
            cout << gc.g.id(c.second) << " ";
            all_nodes.push_back(gc.g.id(c.second));
            cuts_node_vector[cuts_node_vector.size()-1].push_back(c.second);
        }
        cout << endl;
    } 

    assert (gc.nodes.size() == all_nodes.size());

    //vector<vector<int>> fog(cut_maps.size(), vector<int>(cut_maps.size(), 0));
    vector<double> node_ratio_edges_inside;

    for (int i = 0; i < cuts_node_vector.size(); ++i) {
    //for (const auto &m : cuts_node_vector) {
        double edges_inside_cluster = 0.0;
        double all_edges = 0.0;
        for (const auto &n : cuts_node_vector[i]) {
            for (IncEdgeIt e(gc.g, n); e != INVALID; ++e) {
                all_edges = all_edges + 1.0;
                if (count(cuts_node_vector[i].begin(), cuts_node_vector[i].end(), gc.g.target(e)) > 0) {
                    edges_inside_cluster = edges_inside_cluster + 1.0;
                }
            }
        }
        cout << "ei: " << edges_inside_cluster << " all " << all_edges << endl;
        node_ratio_edges_inside.push_back((double)edges_inside_cluster/(double)all_edges);
    }


    for (const auto &r : node_ratio_edges_inside)
        cout << r << endl;

    cout << "singletons: " << n_singletons;

    cout << "All nodes included correctly" << endl;

    ofstream file;
    file.open("cut.txt");
    if (!file) {
        cout << "Cannot open file ";// << OUTPUT_FILE << endl;
        return 1;
    }

    for (const auto &m : cut_maps) {
        for (const auto &c : m) {
            file << gc.g.id(c.second) << " ";
        }
        file << endl;
    }
    file.close();
    

    return 0;
    
}

#pragma clang diagnostic pop
