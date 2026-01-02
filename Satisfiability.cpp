#include<bits/stdc++.h>
using namespace std;

#define int long long

// 2 - Satisfiability.
// Generic Template Using Kosaraju's Algorithm.

struct TS {

    int N;

    vector<vector<int>> graph, reversedGraph; 
    vector<int> components, order, ans; 
    vector<bool> visited;

    TS() {}

    TS (int _N) { 
        initialise(_N); 
    }

    void initialise(int _N) {
        
        N = _N;

        graph.assign(2 * N, vector<int> ());
        reversedGraph.assign(2 * N, vector<int> ());

        components.resize(2 * N);
        visited.resize(2 * N);
        ans.resize(2 * N);
    }

    void addEdge(int u, int v) {

        graph[u].push_back(v);
        reversedGraph[v].push_back(u);

        return;
    }

    // At Least One Of Them Is True.

    void addClauseOR(int i, bool a, int j, bool b) {

        addEdge(i + (a ? N : 0), j + (b ? 0 : N));
        addEdge(j + (b ? N : 0), i + (a ? 0 : N));

        return;
    }

    // Only One Of Them Is True.

    void addClauseXOR(int i, bool a, int j, bool b) {

        addClauseOR(i, a, j, b);
        addClauseOR(i, !a, j, !b);

        return;
    }

    // Both Have Same Value.

    void addClauseAND(int i, bool a, int j, bool b) {

        addClauseXOR(i, !a, j, b);
        return;
    }

    // Topological Sort.

    void dfs(int node) {

        visited[node] = true;

        for (auto neighbor : graph[node]) {

            if (visited[neighbor] == false) 
                dfs(neighbor);
        }

        order.push_back(node);
        return;
    }

    // Extract Strongly Connected Components.

    void stronglyConnectedComponent(int node, int index) {

        visited[node] = true;
        components[node] = index;

        for (auto &neighbor : reversedGraph[node]) {

            if (visited[neighbor] == false) 
                stronglyConnectedComponent(neighbor, index);
        }

        return;
    }

    bool isSatisfiable() {

        fill(visited.begin(), visited.end(), false);

        for (int i = 0; i < 2 * N; i++) {

            if (visited[i] == false) 
                dfs(i);
        }

        fill(visited.begin(), visited.end(), false);
        reverse(order.begin(), order.end());

        int index = 0;

        for (auto &node : order) {

            if (visited[node] == false) 
                stronglyConnectedComponent(node, index++);
        }

        for (int i = 0; i < N; i++) {
            
            if (components[i] == components[i + N]) 
                return false;

            ans[i] = components[i] > components[i + N];
        }

        return true;
    }
};

void runTestCases() {

    
    return;
}

signed main() {

    ios_base::sync_with_stdio(false);
    cin.tie(nullptr);

    int T;
    cin >> T;

    while (T--) 
        runTestCases();

    return 0;
}