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

// PARAMETERS:
int N_NODES = 1000;
int N_ROUNDS = 5;
bool PRINT_PATHS = false;
bool VERBOSE = false;
bool SILENT = false;
bool COMPARE_PARTITION = false;
string PARTITION_FILE;
bool OUTPUT_CUT = false;
string OUTPUT_FILE;
// END PARAMETERS

const double MICROSECS = 1000000.0;

struct InputConfiguration {
    bool load_from_file = false;
    string file_name = "";

    size_t num_nodes = 1000;
};

struct Configuration {
    InputConfiguration input;
    mutable default_random_engine random_engine;
};


// TODO
// I want H -phi tracking
// For that I need to start from scratch (are we there?) We are there!
// and then
// 1) print H-phi
// 2) Adapt a stopping routine


template <class G>
struct CutStats {
    using Node = typename G::Node;
    using Edge = typename G::Edge;
    using Cut = set<Node>;
    using EdgeIt = typename G::EdgeIt;
    using Bisection = set<Node>;
    size_t crossing_edges = 0;
    size_t min_side = 0;
    size_t max_side = 0;

    CutStats(const G &g, size_t num_vertices, const Cut &cut) {
        initialize(g, num_vertices, cut);
    }

    void initialize(const G &g, size_t num_vertices, const Cut &cut) {
        for (EdgeIt e(g); e != INVALID; ++e) {
            if (is_crossing(g, cut, e)) crossing_edges += 1;
        }
        assert(cut.size() <= num_vertices);
        size_t other_size = num_vertices - cut.size();
        min_side = min(cut.size(), other_size);
        max_side = max(cut.size(), other_size);
    }

    static bool is_crossing(const G &g, const Bisection &c, const Edge &e) {
        bool u_in = c.count(g.u(e));
        bool v_in = c.count(g.v(e));
        return u_in != v_in;
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
        return crossing_edges * 1. / min_side;
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

void generate_large_graph(G &g, vector<Node> &nodes) {
    nodes.reserve(N_NODES);
    for (int i = 0; i < N_NODES; i++) {
        nodes.push_back(g.addNode());
    }

    g.addEdge(nodes[0], nodes[1]);
    g.addEdge(nodes[1], nodes[2]);
    g.addEdge(nodes[2], nodes[0]);

    int lim1 = N_NODES / 3;
    int lim2 = 2 * N_NODES / 3;

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
    for (int i = lim2; i < N_NODES; i++) {
        ListGraph::Node u = nodes[i];
        ListGraph::Node v = nodes[2];
        g.addEdge(u, v);
    }
}


struct GraphContext {
    G g;
    //size_t num_vertices;
    vector<Node> nodes;
    Cut reference_cut;
};


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

struct InitializedGraphContext {
    GraphContext &gc;
};

InitializedGraphContext createInputGraph(GraphContext &gc, InputConfiguration config) {
    if (config.load_from_file) {
        parse_chaco_format(config.file_name, gc.g, gc.nodes);

        if (COMPARE_PARTITION) {
            read_partition_file(PARTITION_FILE, gc.nodes, gc.reference_cut);
        }
    } else {
        if (VERBOSE) cout << "Generating graph with " << N_NODES << " nodes." << endl;
        generate_large_graph(gc.g, gc.nodes);
    }
    return {gc};
}

struct CutMatching {
    const Configuration &config;
    GraphContext &gc;
    // Input graph
    CutMatching(InitializedGraphContext &igc, const Configuration &config_) : config(config_), gc(igc.gc) {};

    struct Context {
    public:
        G &g;
        vector<Node> &nodes; // Indexed by file id - 1.
        Cut &reference_cut;
        size_t num_vertices;
        vector<Matchingp> matchings;
        vector<Cutp> cuts;

        explicit Context(G &g_, vector<Node> &nodes_, Cut &reference_cut_ )
        : g(g_), nodes(nodes_), reference_cut(reference_cut_) {

            num_vertices = countNodes(g);
            assert(num_vertices % 2 == 0);
            assert(connected(g));
        }
    };

    struct MatchingContext {
        G &g;
        Node s;
        Node t;
        EdgeMapi capacity;
        CutMap cut_map;
        const size_t num_vertices;
        Snapshot snap; //RAII

        explicit MatchingContext(Context &c)
                : g(c.g),
                  capacity(g),
                  cut_map(g),
                  snap(g),
                  num_vertices(c.num_vertices) {}

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

    // Actually, cut player gets H
// Actually Actually, sure it gets H but it just needs the matchings...
    template<typename M>
    Bisectionp cut_player(const G &g, const vector<unique_ptr<M>> &matchings) {
        if (VERBOSE) cout << "Running Cut player" << endl;
        using MEdgeIt = typename M::EdgeIt;

        NodeMapd probs(g);
        vector<Node> all_nodes;

        uniform_int_distribution<int> uniform_dist(0, 1);
        for (NodeIt n(g); n != INVALID; ++n) {
            all_nodes.push_back(n);
            probs[n] = uniform_dist(config.random_engine) ? 1.0 / all_nodes.size() : -1.0 / all_nodes.size(); // TODO
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
        if (VERBOSE) { print_cut(*b); }

        auto hcs = CutStats<decltype(H)>(H, num_vertices, *b);
        cout << "H expansion: " << hcs.expansion() << ", num cross: " << hcs.crossing_edges << endl;
        auto hscs = CutStats<decltype(H_single)>(H_single, num_vertices, *b);
        cout << "H_single expansion: " << hscs.expansion() << ", num cross: " << hscs.crossing_edges << endl;

        return b;
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

    inline void extract_path_fast(
            const G &g,
            const unique_ptr<Preflow<G, EdgeMapi>> &f,
            NodeNeighborMap &flow_children,
            Node u_orig,
            Node t, // For assertsions
            array<Node, 2> &out_path
    ) {
        if (PRINT_PATHS) cout << "Path: " << g.id(u_orig);
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

// returns capacity that was required
// Maybe: make the binsearch an actual binsearch
    MatchResult matching_player(Context &c, const set<Node> &bisection, ListEdgeSet<G> &m_out) {
        MatchingContext mg(c);
        make_sink_source(mg, bisection);

        unique_ptr<FlowAlgo> p;
        MatchResult mr = bin_search_flows(mg, p);

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

    size_t one_round(Context &c) {
        Bisectionp bisection = cut_player(c.g, c.matchings);

        Matchingp matchingp(new Matching(c.g));

        if (VERBOSE) cout << "Running Matching player" << endl;
        MatchResult mr = matching_player(c, *bisection, *matchingp);
        size_t cap = mr.capacity;
        if (VERBOSE) { print_matching(matchingp); }

        c.matchings.push_back(move(matchingp));
        c.cuts.push_back(move(mr.cut_from_flow));
        return cap;

        // We want to implement that it parses partitions
        // That has nothing to do with the rounds lol
    }

    void print_matching(const Matchingp &m) {
        cout << "Matching player gave the following matching: " << endl;
        for (Matching::EdgeIt e(*m); e != INVALID; ++e) {
            cout << "(" << m->id(m->u(e)) << ", " << m->id(m->v(e)) << "), ";
        }
        cout << endl;
    }

    void print_cut(const Bisection &out_cut) const {
        cout << "Cut player gave the following cut: " << endl;
        for (Node n : out_cut) {
            cout << G::id(n) << ", ";
        }
        cout << endl;
    }

    void print_end_round(int i) const {
        if (VERBOSE) cout << "======================" << endl;
        if(!SILENT) cout << "== End round " << i << " ==" << endl;
        if (VERBOSE) cout << "======================" << endl;
    }

    size_t run_rounds(Context &c) {
        size_t best_cap = 0;
        size_t best_cap_index = 999999;
        for (int i = 0; i < N_ROUNDS; i++) {
            size_t cap = one_round(c);
            print_end_round(i);

            if (cap > best_cap) {
                best_cap = cap;
                best_cap_index = i;
            }
        }

        return best_cap_index;
    }

    void write_cut(const Context &c, const Cut &cut) {
        ofstream file;
        file.open(OUTPUT_FILE);
        if (!file) {
            cout << "Cannot open file " << OUTPUT_FILE << endl;
            return;
        }

        cout << "Writing partition with "
             << c.nodes.size()
             << " nodes to file "
             << OUTPUT_FILE
             << endl;
        for (const auto &n : c.nodes) {
            file << (cut.count(n) ? "1" : "0") << "\n";
        }
        file.close();
    }

    void run() {
        Context c(gc.g, gc.nodes, gc.reference_cut);
        if (N_ROUNDS >= 1) {
            auto best_round = run_rounds(c);
            cout << "The cut with highest capacity required was found on round" << best_round << endl;
            cout << "Best cut sparsity: " << endl;
            auto &best_cut = *c.cuts[best_round];
            CutStats<G>(c.g, c.num_vertices, best_cut).print();
            if (OUTPUT_CUT) { write_cut(c, best_cut); }
        }

        if (COMPARE_PARTITION) { // Output reference cut
            cout << endl
                 << "The given partition achieved the following:"
                 << endl;
            CutStats<G>(c.g, c.num_vertices, c.reference_cut).print();
        }
    }
};

cxxopts::Options create_options() {
    cxxopts::Options options("Janiuk graph partition",
                             "Individual project implementation of thatchapon's paper to find graph partitions. Currently only cut-matching game.");
    options.add_options()
            ("f,file", "File to read graph from", cxxopts::value<std::string>())
            ("n,nodes", "Number of nodes in graph to generate. Should be even. Ignored if -f is set.",
             cxxopts::value<long>()->default_value("100"))

            ("r,rounds", "Number of rounds to run cut-matching game", cxxopts::value<long>()->default_value("5"))

            ("o,output", "Output computed cut into file", cxxopts::value<std::string>())

            ("d,paths", "Whether to print paths")
            ("v,verbose", "Whether to print nodes and cuts (does not include paths)")
            ("s,seed", "Use a seed for RNG (optionally set seed manually)",
             cxxopts::value<int>()->implicit_value("1337"))
            ("S,Silent", "Only output one line of summary at the end")
            ("p,partition", "Partition file to compare with", cxxopts::value<std::string>());
    return options;
}

void parse_options(int argc, char **argv, Configuration &config) {
    auto cmd_options = create_options();
    auto result = cmd_options.parse(argc, argv);

    if (result.count("file")) {
        config.input.load_from_file = true;
        config.input.file_name = result["file"].as<string>();
    }
    if (result.count("nodes"))
        N_NODES = result["nodes"].as<long>();
    if (result.count("rounds"))
        N_ROUNDS = result["rounds"].as<long>();
    if (result.count("verbose"))
        VERBOSE = result["verbose"].as<bool>();
    if (result.count("Silent"))
        SILENT = result["Silent"].as<bool>();
    if (result.count("paths"))
        PRINT_PATHS = result["paths"].as<bool>();
    if (result.count("seed"))
        config.random_engine = default_random_engine(result["seed"].as<int>());
    else
        config.random_engine = default_random_engine(random_device()());
    if (result.count("output")) {
        OUTPUT_CUT = true;
        OUTPUT_FILE = result["output"].as<string>();
    }
    if (result.count("partition")) {
        COMPARE_PARTITION = true;
        PARTITION_FILE = result["partition"].as<string>();
    }
}

// TODO Selecting best cut not only hightest cap
// TODO extract graph creation from algo
// TODO extract final answer presentation from algo
int main(int argc, char **argv) {
    Configuration config;
    parse_options(argc, argv, config);
    GraphContext gc;
    InitializedGraphContext igc = createInputGraph(gc, config.input);

    CutMatching cm(igc, config);
    cm.run();
    return 0;
}

#pragma clang diagnostic pop
