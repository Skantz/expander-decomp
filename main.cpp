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
};
using GraphContextp = unique_ptr<GraphContext>;

// I'd say implementing our own adaptor is more effort, we can just do the snapshot thing
// Actually lets just subdivide manually at the start and we dont even need to restore.
struct SubdividedGraphContext {
    SubdividedGraphContext (GraphContext& gc) :
    origContext(gc),
    nf(sub_g),
    ef(sub_g),
    n_cross_ref(sub_g, INVALID),
    only_splits(sub_g, nf, ef) {} ;
    GraphContext& origContext;
    G sub_g;
    NodeMapb nf;
    EdgeMapb ef;
    NodeMap<Node> n_cross_ref;
    SubGraph<G> only_splits;
    vector<Node> split_vertices;
};

// TODO What chnages will be necessary?
struct RoundReport {
    size_t index;
    size_t capacity_required_for_full_flow;
    double multi_h_expansion;
    double g_expansion;
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
    G& g = sgc.sub_g;

    vector<Edge> edges;
    for (EdgeIt e(g); e != INVALID; ++e) {
        edges.push_back(e);
    }

    for (NodeIt n(g); n != INVALID; ++n) {
        sgc.only_splits.disable(n);
    }

    for(auto& e : edges) {
        Node u = g.u(e);
        Node v = g.v(e);
        g.erase(e);

        Node s = g.addNode();
        sgc.only_splits.enable(s);
        g.addEdge(u, s);
        g.addEdge(s, v);

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
        while (true) {
            auto &tup = flow_children[u].back();
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
    Bisectionp cut_player(const GG &g, const vector<unique_ptr<M>> &given_matchings, double &h_multi_exp_out) {
        l.debug() << "Running Cut player" << endl;
        typename GG::template NodeMap<double> probs(g);
        vector<Node> all_nodes;

        uniform_int_distribution<int> uniform_dist(0, 1);
        for (typename GG::NodeIt n(g); n != INVALID; ++n) {
            all_nodes.push_back(n);
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
        l.progress() << "H expansion: " << hcs.expansion() << ", num cross: " << hcs.crossing_edges << endl;
        h_multi_exp_out = hcs.expansion();
        auto hscs = CutStats<decltype(H_single)>(H_single, num_vertices, *b);
        l.progress() << "H_single expansion: " << hscs.expansion() << ", num cross: " << hscs.crossing_edges << endl;

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
        Bisectionp sub_bisection = cut_player(sgc.only_splits, sub_matchings, h_multi_out_sub);
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
            if(sgc.n_cross_ref[n] != INVALID) {
                report->cut->insert(sgc.n_cross_ref[n]);
            }
        }
        auto cs = CutStats<G>(sgc.origContext.g, sgc.origContext.nodes.size(), *report->cut);
        report->g_expansion = cs.expansion();
        l.progress() << "SUBG cut expansion " << report->g_expansion << endl;
        report->volume = cs.minside_volume();
        l.progress() << "SUBG cut minside volume " << cs.minside_volume() << endl;
        l.progress() << "SUBG cut maxside volume " << cs.maxside_volume() << endl;
        report->relatively_balanced = report->volume > sub_volume_treshold();
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

        if (config.use_volume_treshold && !(last_round->relatively_balanced)) {
            cout << "unbalanced cut" << endl;
            return true;
        }
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
}
vector<list<ListDigraph::Node>> unit_flow(const ListDigraph &g, double h, ListDigraph::NodeMap<double> &sink_node_cap, ListDigraph::ArcMap<double> &cross_edge_source,
               ListDigraph::ArcMap<double> &flow, ListDigraph::NodeMap<double> &node_flow, ListDigraph::NodeMap<int> &degree,
               ListDigraph::ArcMap<double> &edge_cap, vector<list<ListDigraph::Node>> &level_queue, ListDigraph::NodeMap<int> &node_label) {
    bool excess_flow = true;
    unit_start:
    while (excess_flow) {
        excess_flow = false;
        for (int level_iter = 0; level_iter < h - 1; level_iter++) {
            for (auto list_it : level_queue[level_iter]) { //level_queue[level_iter].cbegin(); list_it != level_queue[level_iter].cend(); ++list_it) {
                if (node_flow[list_it] > sink_node_cap[list_it]) {  //Push-relabel(v)
                    excess_flow = true;
                    for (ListDigraph::OutArcIt e(g, list_it); e!=INVALID; ++e) {
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
                        }
                        else {
                            //Relabel v += 1
                            node_label[list_it] += 1;
                            level_queue[level_iter].remove(list_it);
                            level_queue[level_iter + 1].push_back(list_it);
                        }
                        goto unit_start;
                    }
                }
            }
        }
    }
    return level_queue;
}

set<Node> local_flow(const G &ug, const ListDigraph &g, Configuration conf, set<Node>& set_A, double phi, int v, int e) {

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

    double h = int(1 / (phi * log2(e)) * conf.h_factor);//*conf.h_factor);
    vector<list<ListDigraph::Node>> level_queue;
    for (int h_it = 0; h_it < h; h_it++) {
        level_queue.push_back(list<ListDigraph::Node>());
    }
    cout << "local flow: h: " << h << " h factor: " << conf.h_factor << endl;
    assert (level_queue.size() == h && h > 0);

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
        node_flow[n] = 2/phi;
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

    cout << "local flow: h: " << h << endl;
    while (!found_feasible_routing) {
        cout << "Calling unit flow \n";
        level_queue = unit_flow(g, h, sink_node_cap,
                      cross_edge_source,
                      flow,
                      node_flow,
                      degree,
                      edge_cap,
                      level_queue,
                      node_label); 

        assert (level_queue.size() == h);
        if (level_queue[h-1].empty()) {
            cout << "local flow: break on empty level queue at top" << endl;
            for (int i = h - 1; i >= 0; i--) {
                if (level_queue[i].size() > 0)
                    cout << "local flow: level queue level " << i << " : " << level_queue[i].size() << endl;
            }
            cout << "local flow: done break";
            break;
        }

        int i_ = 0;
        for (int i = h - 1; i > 0; --i) {
            for (auto& node : level_queue[i]) {
                int edges_to_next_level = 0;
                int edges_to_any_level  = 0;
                //r (ListDigraph::OutArcIt e(g, *list_it); e!=INVALID; ++e)
                for (ListDigraph::OutArcIt a(g, node); a!=INVALID; ++a) {
                    edges_to_any_level++;
                    if (node_label[g.target(a)])
                        edges_to_next_level++;
                }
                cout << "edges to any level: " << edges_to_any_level << " edges to next level: " << edges_to_next_level << endl;
                if (0 < edges_to_next_level <= 5 * edges_to_any_level * log2(e) / h) {
                    i_ = i;
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
                    cout << "local flow: Upper: " << n_upper_queue_nodes << "Lower: " << n_lower_queue_nodes << endl;
                    if (level_queue[i].size() > 0)
                        cout << "local flow: level queue level " << i << " : " << level_queue[i].size() << endl;
                   set_A.clear();
                   for (int i = h - 1; i > 0; --i) {
                        for (auto& node : level_queue[i]) {
                            assert (!(set_A.count(ug.nodeFromId(g.id(node)))));
                            (set_A).insert(ug.nodeFromId(g.id(node)));
                         }
                    }

                }

            }
       }
       break;
   }

    return set_A;
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

    int sum_all_edges = 0;
    for (const auto &n : cut) {
        for (IncEdgeIt a(g, n); a!=INVALID; ++a) {
            if (cut.count(g.target(a)) > 0 && cut.count(g.source(a)) > 0)
                sum_all_edges++;
            if (cut.count(g.target(a)) > 0 && cut.count(g.source(a)) > 0  && reverse_map[g.source(a)] < reverse_map[g.target(a)]) { //Edge inside cut
                assert (reverse_map[n] != reverse_map[g.target(a)]);
                assert (sg.g.id(reverse_map[g.source(a)]) < sg.nodes.size() && sg.g.id(reverse_map[g.target(a)]) < sg.nodes.size());
                sg.g.addEdge(reverse_map[g.source(a)], reverse_map[g.target(a)]);
                sg.num_edges++;
            }
            //Add self-nodes ?
            //else {
            //    sg.g.addEdge(reverse_map[g.source(a)], reverse_map[g.source(a)]);
            //}
    }   }
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
    cout << "N visited " << n_visited << " g node size " << g.nodes.size() << " cc:  " << cc << endl;
    assert (n_visited == g.nodes.size());
    assert (cc <= g.nodes.size());
    return labels;
}



vector<map<Node, Node>> decomp(GraphContext &gc, ListDigraph &dg, Configuration config, map<Node, Node> map_to_original_graph, vector<set<Node>> cuts, vector<map<Node, Node>> node_maps_to_original_graph) {

    if (gc.nodes.size() == 0)
        return node_maps_to_original_graph;

    if (gc.nodes.size() == 1) {
        node_maps_to_original_graph.push_back(map_to_original_graph);
        return node_maps_to_original_graph;
    }
    if (gc.nodes.size() == 2) {
        map<Node, Node> map_1 = {{gc.g.nodeFromId(0), map_to_original_graph[gc.g.nodeFromId(0)]}};
        map<Node, Node> map_2 = {{gc.g.nodeFromId(0), map_to_original_graph[gc.g.nodeFromId(0)]}};
        node_maps_to_original_graph.push_back(map_1);
        node_maps_to_original_graph.push_back(map_2);
        return node_maps_to_original_graph;
    }

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
        return a->g_expansion < b->g_expansion;
    });

    if (added_node) {
        (*(best_round->cut)).erase(temp_node);
        gc.g.erase(temp_edge);
        gc.g.erase(temp_node);
        gc.nodes.pop_back();
        gc.num_edges--;
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

            } else {
                ListDigraph dg_;
                digraph_from_graph(gc.g, dg_);
                cout << "Call local flow with cut of size: " << (*(best_round->cut)).size() << endl;
                *(best_round->cut) = local_flow(gc.g, dg_, config, *(best_round->cut), config.G_phi_target, gc.nodes.size(), gc.num_edges);
                cout << "After local flow, cut is reduced to n nodes: " << (*(best_round->cut)).size() << endl;
                assert (((*(best_round->cut)).size()) != 0);
                
                GraphContext V_over_A;
                map<Node, Node> new_map = graph_from_cut(gc.g, V_over_A, (*best_round->cut), map_to_original_graph, true);
                assert (V_over_A.nodes.size() > 0);
                node_maps_to_original_graph.push_back(new_map);
                map <Node, Node> new_map_;

                vector<set<Node>> labels = find_connected_components(V_over_A);
                for (auto& sg_cut : labels) {
                    cout << "decomp on cc (CM)" << endl;
                    GraphContext sg;
                    map<Node, Node> new_new_map = graph_from_cut(V_over_A.g, sg, sg_cut, new_map);
                    node_maps_to_original_graph.push_back(new_new_map);
                    //node_maps_to_original_graph =
                    decomp(sg, dg, config, new_new_map, cuts, node_maps_to_original_graph);
                }
            }
        } else {
            if (config.use_volume_treshold && !((*(cm.sub_past_rounds.end()-1))->relatively_balanced)) {
                ListDigraph dg_;
                digraph_from_graph(gc.g, dg_);
                cout << "Call local flow with cut of size: " << (*(best_round->cut)).size() << endl;
                *(best_round->cut) = local_flow(gc.g, dg_, config, *(best_round->cut), config.G_phi_target, gc.nodes.size(), gc.num_edges);
                cout << "After local flow, cut is reduced to n nodes: " << (*(best_round->cut)).size() << endl;
                //assert (((*best_round->cut)).size() != 0);
                
                GraphContext dummy;
                map<Node, Node> finished_cut_map = graph_from_cut(gc.g, dummy, *(best_round->cut), map_to_original_graph, false);
                node_maps_to_original_graph.push_back(finished_cut_map);
                GraphContext V_over_A;
                map<Node, Node> new_map = graph_from_cut(gc.g, V_over_A, *(best_round->cut), map_to_original_graph, true);
                assert (V_over_A.nodes.size() > 0);
                node_maps_to_original_graph.push_back(new_map);
                map <Node, Node> new_map_;

                vector<set<Node>> labels = find_connected_components(V_over_A);
                for (auto& sg_cut : labels) {
                    cout << "decomp on cc (CM)" << endl;
                    GraphContext sg;
                    map<Node, Node> new_new_map = graph_from_cut(V_over_A.g, sg, sg_cut, new_map);
                    node_maps_to_original_graph.push_back(new_new_map);
           
                    decomp(sg, dg, config, new_new_map, cuts, node_maps_to_original_graph);
                }
 
            }
            else {
            
            cout << "CASE2 Goodenough balanced cut" << endl;
            GraphContext A;
            cout << "Create map to original graph" << endl;
            map<Node, Node> new_map = graph_from_cut(gc.g, A, *(best_round->cut), map_to_original_graph);
            assert (A.nodes.size() == (*(best_round->cut)).size());
            cout << "Decomp on A" << endl;
            map <Node, Node> new_map_;
            vector<set<Node>> subgraph_maps = find_connected_components(A);
            for (auto &sg_cut : subgraph_maps) {
                GraphContext sg;
                map<Node, Node> new_new_map = graph_from_cut(A.g, sg, sg_cut, new_map);
                node_maps_to_original_graph.push_back(new_new_map);
            
                cout << "Decomp on graph with n: " << sg.nodes.size() << " e: " << sg.num_edges << endl;
                assert (connected( sg.g ));
                decomp(sg, dg, config, new_new_map, cuts, node_maps_to_original_graph);
            }

    
            GraphContext R;
            cout << "(R) create map to original graph" << endl;
            new_map = graph_from_cut(gc.g, R, *(best_round->cut), map_to_original_graph, true);
            cout << "Decomp on R" << endl;
            subgraph_maps = find_connected_components(R);
            for (auto &sg_cut : subgraph_maps) {
                GraphContext sg_R;
                map<Node, Node> new_new_map_R = graph_from_cut(R.g, sg_R, sg_cut, new_map);
                node_maps_to_original_graph.push_back(new_new_map_R);

                cout << "Decomp on graph with n: " << sg_R.nodes.size() << " e: " << sg_R.num_edges << endl;
                assert ( connected ( sg_R.g) );
                decomp(sg_R, dg, config, new_new_map_R, cuts, node_maps_to_original_graph);
            }
            assert (A.nodes.size() + R.nodes.size() == gc.nodes.size() );
        }}
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

    vector<vector<Node>> cuts_node_vector;
    for (const auto &m : cut_maps) {
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
        double edges_inside_cluster = 1.0;
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

  
    cout << "All nodes included correctly" << endl;

    for (const auto &r : node_ratio_edges_inside)
        cout << r << endl;

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

    default_random_engine random_engine = config.seed_randomness
                    ? default_random_engine(config.seed)
                    : default_random_engine(random_device()());
    CutMatching cm(gc, config, random_engine);
    cm.run();

    // TODO searching conditions different depending on if hit H
    assert(!cm.sub_past_rounds.empty());
    // Best by expnansion
    auto& best_round = *max_element(cm.sub_past_rounds.begin(), cm.sub_past_rounds.end(), [](auto &a, auto &b) {
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
                local_flow(gc.g, dg, config, *(best_round->cut), config.G_phi_target, gc.nodes.size(), gc.num_edges);
            }
        } else {
            cout << "CASE2 Goodenough balanced cut" << endl;

        }

    }

    cout << "DEBUG LOCAL FLOW" << "\n";
    local_flow(gc.g, dg, config, *(best_round->cut), config.G_phi_target, gc.nodes.size(), gc.num_edges);
    cout << "FINISHED LOCAL FLOW" << "\n";
    //if (OUTPUT_CUT) { write_cut(gc.nodes, *best_cut); }
    /*
    if (config.compare_partition) {
        read_partition_file(config.partition_file, gc.nodes, gc.reference_cut);
        cout << endl
             << "The given partition achieved the following:"
             << endl;
        CutStats<G>(gc.g, gc.nodes.size(), gc.reference_cut).print();
    }
    */
    return 0;
}

#pragma clang diagnostic pop
