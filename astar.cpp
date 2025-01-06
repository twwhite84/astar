#include <algorithm>
#include <cassert>
#include <functional>
#include <iostream>
#include <map>
#include <numeric>
#include <optional>
#include <queue>
#include <string>
#include <tuple>
#include <vector>

using namespace std;

/* -------------------------------------------------------------------------- */

using State = vector<int>;
using Heuristic = function<int(State, State)>;
enum class Move { N = 'U', E = 'R', S = 'D', W = 'L' };

/* -------------------------------------------------------------------------- */

class SearchNode {
   private:
    vector<State> states;
    vector<Move> moves;
    State goal;
    optional<Heuristic> heuristic;

   public:
    SearchNode() : states{}, moves{}, goal(), heuristic() {}

    SearchNode(State start, State goal, optional<Heuristic> h = nullopt)
        : states{start}, moves{}, goal(goal), heuristic(h) {}

    bool operator>(const SearchNode& other) const {
        return this->getFCost() > other.getFCost();
    }

    State getState() const { return states[0]; }

    vector<State> getStates() const { return states; }

    int getPathlength() const { return states.size() - 1; }

    int getFCost() const {
        int g = getPathlength();
        int h = 0;
        if (heuristic) {
            h = (*heuristic)(getState(), goal);
        }
        int f = g + h;
        return f;
    }

    void expand(State state, Move move) {
        states.emplace(states.begin(), state);
        moves.emplace_back(move);
    }

    string getPath(void) const {
        string formatted_path = "";
        for (Move move : moves) {
            formatted_path += static_cast<char>(move);
        }
        return formatted_path;
    }
};

/* -------------------------------------------------------------------------- */

tuple<int, int> findTile(State state, int tile) {
    int i, j;
    bool done = false;
    for (i = 0; i < 3; i++) {
        for (j = 0; j < 3; j++) {
            if (state[3 * i + j] == tile) {
                done = true;
                break;
            }
        }
        if (done) break;
    }
    return {i, j};
}

/* -------------------------------------------------------------------------- */

int computeManhattan(State state, State goal) {
    vector<int> dists = {};
    for (int tile : state) {
        if (tile == 0) {
            continue;
        }
        int x_S, y_S, x_G, y_G;
        tie(x_S, y_S) = findTile(state, tile);
        tie(x_G, y_G) = findTile(goal, tile);
        int D = abs(x_S - x_G) + abs(y_S - y_G);
        dists.emplace_back(D);
    }
    int sum = accumulate(dists.begin(), dists.end(), 0);
    return sum;
}

/* -------------------------------------------------------------------------- */

int computeMisplacedTiles(State state, State goal) {
    int n_misplaced = 0;
    for (int i = 0; i < int(state.size()); i++) {
        if (state[i] == 0) continue;
        if (state[i] != goal[i]) {
            n_misplaced += 1;
        }
    }
    return n_misplaced;
}

/* -------------------------------------------------------------------------- */

State makeMove(State state, Move move) {
    State new_state = state;
    int i, j;
    tie(i, j) = findTile(state, 0);

    // swap position with adjacent tile according to move direction
    if (move == Move::N) {
        int tile_pos = new_state[3 * (i - 1) + j];
        new_state[3 * (i - 1) + j] = 0;
        new_state[3 * i + j] = tile_pos;
    }

    if (move == Move::E) {
        int tile_pos = new_state[3 * i + j + 1];
        new_state[3 * i + j + 1] = 0;
        new_state[3 * i + j] = tile_pos;
    }

    if (move == Move::S) {
        int tile_pos = new_state[3 * (i + 1) + j];
        new_state[3 * (i + 1) + j] = 0;
        new_state[3 * i + j] = tile_pos;
    }

    if (move == Move::W) {
        int tile_pos = new_state[3 * i + j - 1];
        new_state[3 * i + j - 1] = 0;
        new_state[3 * i + j] = tile_pos;
    }

    return new_state;
}

/* -------------------------------------------------------------------------- */

vector<Move> findValidMoves(State state) {
    map<tuple<int, int>, vector<Move>> valid_moves = {
        {{0, 0}, {Move::E, Move::S}},
        {{0, 1}, {Move::E, Move::S, Move::W}},
        {{0, 2}, {Move::S, Move::W}},
        {{1, 0}, {Move::N, Move::E, Move::S}},
        {{1, 1}, {Move::N, Move::E, Move::S, Move::W}},
        {{1, 2}, {Move::N, Move::S, Move::W}},
        {{2, 0}, {Move::N, Move::E}},
        {{2, 1}, {Move::N, Move::E, Move::W}},
        {{2, 2}, {Move::N, Move::W}},
    };

    return valid_moves[findTile(state, 0)];
}

/* -------------------------------------------------------------------------- */

class PathSearch {
   private:
    int step;
    SearchNode dequeued;
    vector<SearchNode> Q;
    vector<State> expanded;
    int max_Q_length;

    void updateMaxQLength() {
        if (int(Q.size()) > max_Q_length) {
            max_Q_length++;
        }
    }

    void reset() {
        step = 0;
        dequeued = SearchNode();
        Q = {};
        expanded = {};
        max_Q_length = 0;
    }

   public:
    void search(State start, State goal, optional<Heuristic> h = nullopt,
                optional<int> max_step = nullopt) {
        reset();

        // 1. initialise Q to search node (S), expanded list to empty
        dequeued = SearchNode(start, goal, h);
        make_heap(Q.begin(), Q.end(), greater<SearchNode>());
        Q.emplace_back(dequeued);
        push_heap(Q.begin(), Q.end(), greater<SearchNode>());
        updateMaxQLength();

        // 2. Q empty? Fail. Else dequeue (N) with shortest path length
        while (Q.size() > 0) {
            if (max_step && step >= max_step) {
                cout << "Max Step Exceeded, Cancelling Search..." << endl;
                reset();
                break;
            }

            step += 1;
            dequeued = Q.front();
            pop_heap(Q.begin(), Q.end(), greater<SearchNode>());
            Q.pop_back();
            vector<int> state_N = dequeued.getState();

            // 3. state(N) goal? return (N)
            if (state_N == goal) {
                expanded.emplace_back(goal);
                break;
            }

            // 4. state(N) in expanded? skip. else update expanded
            auto iter = find(expanded.begin(), expanded.end(), state_N);
            if (iter != expanded.end()) {
                continue;
            } else {
                expanded.emplace_back(dequeued.getState());
            }

            // 5. make new search nodes for state(N) children not in expanded
            vector<tuple<State, Move>> expansions = {};
            for (const Move& move : findValidMoves(state_N)) {
                State state = makeMove(state_N, move);
                auto iter = find(expanded.begin(), expanded.end(), state);
                if (iter == expanded.end()) {
                    expansions.emplace_back(state, move);
                }
            }

            for (tuple<State, Move>& pair : expansions) {
                // if state in states of Q's searchnodes, skip
                bool state_in_Q = false;
                for (SearchNode& Q_snode : Q) {
                    if (Q_snode.getState() == get<0>(pair)) {
                        state_in_Q = true;
                        break;
                    }
                }
                if (!state_in_Q) {
                    SearchNode snode = dequeued;
                    snode.expand(get<0>(pair), get<1>(pair));
                    Q.emplace_back(snode);
                    push_heap(Q.begin(), Q.end(), greater<SearchNode>());
                    updateMaxQLength();
                }
            }
        }
    }

    int getFCost() const { return dequeued.getFCost(); }

    int getPathLength() const { return dequeued.getPathlength(); }

    string getPath() const { return dequeued.getPath(); }

    int getNExpansions() const { return expanded.size(); }

    int getMaxQLength() const { return max_Q_length; }
};

/* -------------------------------------------------------------------------- */

// TESTS

void testFindTile() {
    cout << "TEST: findTile..." << endl;
    tuple<int, int> actual, expected;
    State start = {1, 2, 3, 4, 0, 5, 6, 7, 8};
    int tile;

    tile = 0;
    expected = make_tuple(1, 1);
    actual = findTile(start, tile);
    assert(actual == expected);

    tile = 1;
    expected = make_tuple(0, 0);
    actual = findTile(start, tile);
    assert(actual == expected);
}

/* -------------------------------------------------------------------------- */

void testMakeMove() {
    cout << "TEST: makeMove..." << endl;
    State expected, actual;
    State start = {1, 2, 3, 4, 0, 5, 6, 7, 8};

    // up
    expected = {1, 0, 3, 4, 2, 5, 6, 7, 8};
    actual = makeMove(start, Move::N);
    assert(actual == expected);

    // right
    expected = {1, 2, 3, 4, 5, 0, 6, 7, 8};
    actual = makeMove(start, Move::E);
    assert(actual == expected);

    // down
    expected = {1, 2, 3, 4, 7, 5, 6, 0, 8};
    actual = makeMove(start, Move::S);
    assert(actual == expected);

    // left
    expected = {1, 2, 3, 0, 4, 5, 6, 7, 8};
    actual = makeMove(start, Move::W);
    assert(actual == expected);
}

/* -------------------------------------------------------------------------- */

void testFindValidMoves() {
    cout << "TEST: findValidMoves..." << endl;
    vector<Move> expected, actual;

    // black at top-left
    expected = {Move::E, Move::S};
    actual = findValidMoves(vector<int>({0, 1, 2, 3, 4, 5, 6, 7, 8}));
    assert(actual == expected);

    // black at top
    expected = {Move::E, Move::S, Move::W};
    actual = findValidMoves(vector<int>({1, 0, 2, 3, 4, 5, 6, 7, 8}));
    assert(actual == expected);

    // black at top-right
    expected = {Move::S, Move::W};
    actual = findValidMoves(vector<int>({1, 2, 0, 3, 4, 5, 6, 7, 8}));
    assert(actual == expected);

    // black at left
    expected = {Move::N, Move::E, Move::S};
    actual = findValidMoves(vector<int>({1, 2, 3, 0, 4, 5, 6, 7, 8}));
    assert(actual == expected);

    // black at center
    expected = {Move::N, Move::E, Move::S, Move::W};
    actual = findValidMoves(vector<int>({1, 2, 3, 4, 0, 5, 6, 7, 8}));
    assert(actual == expected);

    // black at right
    expected = {Move::N, Move::S, Move::W};
    actual = findValidMoves(vector<int>({1, 2, 3, 4, 5, 0, 6, 7, 8}));
    assert(actual == expected);

    // black at bottom-left
    expected = {Move::N, Move::E};
    actual = findValidMoves(vector<int>({1, 2, 3, 4, 5, 6, 0, 7, 8}));
    assert(actual == expected);

    // black at bottom
    expected = {Move::N, Move::E, Move::W};
    actual = findValidMoves(vector<int>({1, 2, 3, 4, 5, 6, 7, 0, 8}));
    assert(actual == expected);

    // black at bottom-right
    expected = {Move::N, Move::W};
    actual = findValidMoves(vector<int>({1, 2, 3, 4, 5, 6, 7, 8, 0}));
    assert(actual == expected);
}

/* -------------------------------------------------------------------------- */

void testGetPathLength() {
    cout << "TEST: getPathLength..." << endl;
    int expected, actual;
    State start = vector<int>({1, 2, 3, 4, 0, 5, 6, 7, 8});
    State goal = vector<int>({1, 0, 3, 4, 2, 5, 6, 7, 8});

    // for UC, the "f-cost" is just g
    // calling getPathlength() and getFCost() should give the same result
    SearchNode uc_snode = SearchNode(start, goal);
    expected = 0;
    actual = uc_snode.getFCost();
    assert(actual == expected);
    actual = uc_snode.getPathlength();
    assert(actual == expected);
    assert(uc_snode.getFCost() == uc_snode.getPathlength());

    uc_snode.expand(goal, Move::N);
    expected = 1;
    actual = uc_snode.getFCost();
    assert(actual == expected);
    actual = uc_snode.getPathlength();
    assert(actual == expected);
    assert(uc_snode.getFCost() == uc_snode.getPathlength());

    // for A*, the initial f-cost should be the heuristic, not 0
    SearchNode astar_manhattan = SearchNode(start, goal, computeManhattan);
    expected = 0;
    actual = astar_manhattan.getPathlength();
    assert(actual == expected);
    expected = 1;
    actual = astar_manhattan.getFCost();
    assert(actual == expected);
    assert(astar_manhattan.getPathlength() != astar_manhattan.getFCost());

    // for A*, the final f-cost should be the actual accumulated length g
    astar_manhattan.expand(goal, Move::N);
    expected = 1;
    actual = astar_manhattan.getPathlength();
    assert(actual == expected);
    expected = 1;
    actual = astar_manhattan.getFCost();
    assert(actual == expected);
    assert(astar_manhattan.getPathlength() == astar_manhattan.getFCost());

    // above A* rules should work the same way if the heuristic is swapped
    SearchNode astar_misplaced = SearchNode(start, goal, computeMisplacedTiles);
    expected = 0;
    actual = astar_misplaced.getPathlength();
    assert(actual == expected);
    expected = 1;
    actual = astar_misplaced.getFCost();
    assert(actual == expected);
    assert(astar_misplaced.getPathlength() != astar_misplaced.getFCost());

    astar_misplaced.expand(goal, Move::N);
    expected = 1;
    actual = astar_misplaced.getPathlength();
    assert(actual == expected);
    expected = 1;
    actual = astar_misplaced.getFCost();
    assert(actual == expected);
    assert(astar_misplaced.getPathlength() == astar_misplaced.getFCost());
}

/* -------------------------------------------------------------------------- */

void testComputeManhattan() {
    cout << "TEST: computeManhattan..." << endl;
    int actual, expected;
    State goal = {1, 2, 3, 8, 0, 4, 7, 6, 5};

    State left = {2, 8, 3, 1, 6, 4, 0, 7, 5};
    expected = 6;
    actual = computeManhattan(left, goal);
    assert(actual == expected);

    State up = {2, 8, 3, 1, 0, 4, 7, 6, 5};
    expected = 4;
    actual = computeManhattan(up, goal);
    assert(actual == expected);

    State right = {2, 8, 3, 1, 6, 4, 7, 5, 0};
    expected = 6;
    actual = computeManhattan(right, goal);
    assert(actual == expected);

    expected = 0;
    actual = computeManhattan(goal, goal);
    assert(actual == expected);

    expected = 0;
    actual = computeManhattan(left, left);
    assert(actual == expected);
}

/* -------------------------------------------------------------------------- */

void testPathSearch() {
    cout << "TEST: pathSearch..." << endl;

    // example sequence
    cout << "\n====== EXAMPLE SEQUENCE ======" << endl;
    State start = {1, 3, 4, 8, 0, 5, 7, 2, 6};
    State goal = {1, 2, 3, 8, 0, 4, 7, 6, 5};
    PathSearch ps = PathSearch();

    cout << "\n--- Uniform Cost ---" << endl;
    ps.search(start, goal);
    cout << "Max Q Length: " << ps.getMaxQLength() << endl;
    cout << "Path Length: " << ps.getPathLength() << endl;
    cout << "n Expansions: " << ps.getNExpansions() << endl;
    cout << "F-Cost: " << ps.getFCost() << endl;
    cout << "Path:  " << ps.getPath() << endl;

    cout << "\n--- A* Manhattan ---" << endl;
    ps.search(start, goal, computeManhattan);
    cout << "Max Q Length: " << ps.getMaxQLength() << endl;
    cout << "Path Length: " << ps.getPathLength() << endl;
    cout << "n Expansions: " << ps.getNExpansions() << endl;
    cout << "F-Cost: " << ps.getFCost() << endl;
    cout << "Path:  " << ps.getPath() << endl;

    cout << "\n--- A* Missing Tiles ---" << endl;
    ps.search(start, goal, computeMisplacedTiles);
    cout << "Max Q Length: " << ps.getMaxQLength() << endl;
    cout << "Path Length: " << ps.getPathLength() << endl;
    cout << "n Expansions: " << ps.getNExpansions() << endl;
    cout << "F-Cost: " << ps.getFCost() << endl;
    cout << "Path:  " << ps.getPath() << endl;

    // test 1
    goal = {1, 2, 3, 4, 5, 6, 7, 8, 0};
    cout << "\n====== TEST 1 ======" << endl;
    start = {1, 2, 0, 4, 8, 3, 7, 6, 5};

    cout << "\n--- Uniform Cost ---" << endl;
    ps.search(start, goal);
    cout << "Max Q Length: " << ps.getMaxQLength() << endl;
    cout << "Path Length: " << ps.getPathLength() << endl;
    cout << "n Expansions: " << ps.getNExpansions() << endl;
    cout << "F-Cost: " << ps.getFCost() << endl;
    cout << "Path:  " << ps.getPath() << endl;

    cout << "\n--- A* Manhattan ---" << endl;
    ps.search(start, goal, computeManhattan);
    cout << "Max Q Length: " << ps.getMaxQLength() << endl;
    cout << "Path Length: " << ps.getPathLength() << endl;
    cout << "n Expansions: " << ps.getNExpansions() << endl;
    cout << "F-Cost: " << ps.getFCost() << endl;
    cout << "Path:  " << ps.getPath() << endl;

    cout << "\n--- A* Missing Tiles ---" << endl;
    ps.search(start, goal, computeMisplacedTiles);
    cout << "Max Q Length: " << ps.getMaxQLength() << endl;
    cout << "Path Length: " << ps.getPathLength() << endl;
    cout << "n Expansions: " << ps.getNExpansions() << endl;
    cout << "F-Cost: " << ps.getFCost() << endl;
    cout << "Path:  " << ps.getPath() << endl;

    // test 2
    cout << "\n====== TEST 2 ======" << endl;
    start = {2, 0, 8, 1, 3, 5, 4, 6, 7};

    cout << "\n--- Uniform Cost ---" << endl;
    ps.search(start, goal);
    cout << "Max Q Length: " << ps.getMaxQLength() << endl;
    cout << "Path Length: " << ps.getPathLength() << endl;
    cout << "n Expansions: " << ps.getNExpansions() << endl;
    cout << "F-Cost: " << ps.getFCost() << endl;
    cout << "Path:  " << ps.getPath() << endl;

    cout << "\n--- A* Manhattan ---" << endl;
    ps.search(start, goal, computeManhattan);
    cout << "Max Q Length: " << ps.getMaxQLength() << endl;
    cout << "Path Length: " << ps.getPathLength() << endl;
    cout << "n Expansions: " << ps.getNExpansions() << endl;
    cout << "F-Cost: " << ps.getFCost() << endl;
    cout << "Path:  " << ps.getPath() << endl;

    cout << "\n--- A* Missing Tiles ---" << endl;
    ps.search(start, goal, computeMisplacedTiles);
    cout << "Max Q Length: " << ps.getMaxQLength() << endl;
    cout << "Path Length: " << ps.getPathLength() << endl;
    cout << "n Expansions: " << ps.getNExpansions() << endl;
    cout << "F-Cost: " << ps.getFCost() << endl;
    cout << "Path:  " << ps.getPath() << endl;

    // test 3
    cout << "\n====== TEST 3 ======" << endl;
    start = {7, 0, 4, 8, 5, 1, 6, 3, 2};

    cout << "\n--- Uniform Cost ---" << endl;
    ps.search(start, goal, nullopt, 5000);
    cout << "Max Q Length: " << ps.getMaxQLength() << endl;
    cout << "Path Length: " << ps.getPathLength() << endl;
    cout << "n Expansions: " << ps.getNExpansions() << endl;
    cout << "F-Cost: " << ps.getFCost() << endl;
    cout << "Path:  " << ps.getPath() << endl;

    cout << "\n--- A* Manhattan ---" << endl;
    ps.search(start, goal, computeManhattan);
    cout << "Max Q Length: " << ps.getMaxQLength() << endl;
    cout << "Path Length: " << ps.getPathLength() << endl;
    cout << "n Expansions: " << ps.getNExpansions() << endl;
    cout << "F-Cost: " << ps.getFCost() << endl;
    cout << "Path:  " << ps.getPath() << endl;

    cout << "\n--- A* Missing Tiles ---" << endl;
    ps.search(start, goal, computeMisplacedTiles);
    cout << "Max Q Length: " << ps.getMaxQLength() << endl;
    cout << "Path Length: " << ps.getPathLength() << endl;
    cout << "n Expansions: " << ps.getNExpansions() << endl;
    cout << "F-Cost: " << ps.getFCost() << endl;
    cout << "Path:  " << ps.getPath() << endl;

    // test 4
    cout << "\n====== TEST 4 ======" << endl;
    start = {5, 3, 6, 4, 0, 7, 1, 8, 2};

    cout << "\n--- Uniform Cost ---" << endl;
    ps.search(start, goal, nullopt, 5000);
    cout << "Max Q Length: " << ps.getMaxQLength() << endl;
    cout << "Path Length: " << ps.getPathLength() << endl;
    cout << "n Expansions: " << ps.getNExpansions() << endl;
    cout << "F-Cost: " << ps.getFCost() << endl;
    cout << "Path:  " << ps.getPath() << endl;

    cout << "\n--- A* Manhattan ---" << endl;
    ps.search(start, goal, computeManhattan);
    cout << "Max Q Length: " << ps.getMaxQLength() << endl;
    cout << "Path Length: " << ps.getPathLength() << endl;
    cout << "n Expansions: " << ps.getNExpansions() << endl;
    cout << "F-Cost: " << ps.getFCost() << endl;
    cout << "Path:  " << ps.getPath() << endl;

    cout << "\n--- A* Missing Tiles ---" << endl;
    ps.search(start, goal, computeMisplacedTiles);
    cout << "Max Q Length: " << ps.getMaxQLength() << endl;
    cout << "Path Length: " << ps.getPathLength() << endl;
    cout << "n Expansions: " << ps.getNExpansions() << endl;
    cout << "F-Cost: " << ps.getFCost() << endl;
    cout << "Path:  " << ps.getPath() << endl;

    // test 5
    cout << "\n====== TEST 5 ======" << endl;
    start = {6, 3, 8, 5, 4, 1, 7, 2, 0};

    cout << "\n--- Uniform Cost ---" << endl;
    ps.search(start, goal, nullopt, 5000);
    cout << "Max Q Length: " << ps.getMaxQLength() << endl;
    cout << "Path Length: " << ps.getPathLength() << endl;
    cout << "n Expansions: " << ps.getNExpansions() << endl;
    cout << "F-Cost: " << ps.getFCost() << endl;
    cout << "Path:  " << ps.getPath() << endl;

    cout << "\n--- A* Manhattan ---" << endl;
    ps.search(start, goal, computeManhattan);
    cout << "Max Q Length: " << ps.getMaxQLength() << endl;
    cout << "Path Length: " << ps.getPathLength() << endl;
    cout << "n Expansions: " << ps.getNExpansions() << endl;
    cout << "F-Cost: " << ps.getFCost() << endl;
    cout << "Path:  " << ps.getPath() << endl;

    cout << "\n--- A* Missing Tiles ---" << endl;
    ps.search(start, goal, computeMisplacedTiles, 5000);
    cout << "Max Q Length: " << ps.getMaxQLength() << endl;
    cout << "Path Length: " << ps.getPathLength() << endl;
    cout << "n Expansions: " << ps.getNExpansions() << endl;
    cout << "F-Cost: " << ps.getFCost() << endl;
    cout << "Path:  " << ps.getPath() << endl;
}

/* -------------------------------------------------------------------------- */

void testSearchNodeComparator(void) {
    cout << "TEST: comparator..." << endl;
    int expected, actual;
    vector<SearchNode> Q = {};
    make_heap(Q.begin(), Q.end(), greater<SearchNode>());

    State start = vector<int>({1, 2, 3, 4, 0, 5, 6, 7, 8});
    State goal = vector<int>({1, 0, 3, 4, 2, 5, 6, 7, 8});
    SearchNode snode_shorter = SearchNode(start, goal);
    SearchNode snode_longer = SearchNode(start, goal);
    snode_longer.expand(goal, Move::N);
    assert(snode_shorter.getFCost() == 0);
    assert(snode_longer.getFCost() == 1);

    Q.emplace_back(snode_longer);
    push_heap(Q.begin(), Q.end(), greater<SearchNode>());
    Q.emplace_back(snode_shorter);
    push_heap(Q.begin(), Q.end(), greater<SearchNode>());

    // longer would be at front but push_heap sorted so front returns shorter
    SearchNode q = Q.front();
    expected = snode_shorter.getFCost();
    actual = q.getFCost();
    assert(actual == expected);
}

/* -------------------------------------------------------------------------- */

int main() {
    testFindTile();
    testMakeMove();
    testFindValidMoves();
    testComputeManhattan();
    testGetPathLength();
    testPathSearch();
    testSearchNodeComparator();
    return 0;
}