#include<bits/stdc++.h>
using namespace std;

#define int long long

const int INF = 1e12;
const int maxN = 1e5 + 10;

using Pair = array<int, 2>;

// MCMF Theorem.
// USACO Guide (KACTL's Implementation) + CP Algorithms.

struct Edge {

    int from, to, reversed;
    int capacity, cost, flow;
};

struct MCMF {

	int N;

	vector<vector<Edge>> edges;
	vector<int> seen, parent_node, parent_edge;
	vector<int> distances, potentials;
	vector<Edge*> parents;

	MCMF(int N) : N (N), edges (N), seen (N), distances (N), potentials (N), parents (N), parent_node (N), parent_edge (N) {}

	void addEdge(int from, int to, int capacity, int cost) {

        if (from != to) {

            edges[from].push_back(Edge {from, to, edges[to].size(), capacity, cost, 0});
            edges[to].push_back(Edge {to, from, edges[from].size() -1, 0, -cost, 0});
        }

        return;
	}

    bool path_CP(int source, int sink) {

        fill(distances.begin(), distances.end(), INF);
        fill(parent_node.begin(), parent_node.end(), -1);

        vector<bool> in_queue (N);
        queue<int> q;

        distances[source] = 0;
        q.push(source);
        in_queue[source] = 1;

        while (q.empty() == 0) {

            int node = q.front();
            q.pop();

            in_queue[node] = 0;

            for (int i = 0; i < edges[node].size(); ++i) {

                Edge &e = edges[node][i];

                if ((e.capacity > e.flow) and (distances[e.to] > (distances[node] + e.cost))) {

                    distances[e.to] = distances[node] + e.cost;
                    parent_node[e.to] = node;
                    parent_edge[e.to] = i;
                    
                    if (in_queue[e.to] == 0) {

                        q.push(e.to);
                        in_queue[e.to] = true;
                    }
                }
            }
        }

        return distances[sink] != INF;
    }

    Pair maxFlow_CP(int source, int sink) {

        int flow = 0;
        int cost = 0;

        while ((path_CP(source, sink) == 1) and (distances[sink] < 0)) {
         
            int push = INF;
            int current = sink;

            while (current != source) {

                int parent = parent_node[current];
                int index = parent_edge[current];

                push = min(push, edges[parent][index].capacity - edges[parent][index].flow);
                current = parent;
            }

            flow += push;
            cost += push * distances[sink];
            current = sink;

            while (current != source) {

                int parent = parent_node[current];
                int index = parent_edge[current];

                edges[parent][index].flow += push;

                int indexR = edges[parent][index].reversed;
                edges[current][indexR].flow -= push;

                current = parent;
            }
        }

        return {flow, cost};
    }

    void path(int source) {

        fill(seen.begin(), seen.end(), 0);
        fill(distances.begin(), distances.end(), INF);

        distances[source] = 0;
        
        priority_queue<Pair, vector<Pair>, greater<Pair>> pq;
        pq.push({0, source});

        while (pq.empty() == 0) {

            auto [distance, node] = pq.top();
            pq.pop();

            if (distance > distances[node]) 
                continue; 

            seen[node] = 1;
            
            for (auto &e : edges[node]) {

                int distance_ = distances[node] + e.cost + potentials[node] - potentials[e.to];
                
                if ((e.capacity > e.flow) and (distance_ < distances[e.to])) {

                    distances[e.to] = distance_;
                    parents[e.to] = &e;
                    pq.push({distance_, e.to});
                }
            }
        }

        for (int i = 0; i < N; ++i) {

            if (distances[i] != INF) 
                potentials[i] += distances[i];
        }

        return;
    }

    Pair maxFlow_USACO(int source, int sink) {

        int netFlow = 0, netCost = 0;

        while (path(source), seen[sink]) {

            int push = INF;
            
            for (Edge* x = parents[sink]; x != 0; x = parents[x -> from])
                push = min(push, x->capacity - x->flow);

            netFlow += push;
            
            for (Edge* x = parents[sink]; x != 0; x = parents[x -> from]) {

                x -> flow += push;
                edges[x -> to][x -> reversed].flow -= push;
            }
        }

        for (int i = 0; i < N; ++i) {

            for (auto &e : edges[i]) 
                netCost += e.cost * e.flow;
        }

        return {netFlow, netCost / 2};
    }

    void setPotentials(int s) {

        fill(potentials.begin(), potentials.end(), INF); 
        potentials[s] = 0;

        int it = N, changed = 1;
        
        while ((changed-- > 0) and (it-- > 0)) {

            changed = 0;

            for (int i = 0; i < N; ++i) {

                if (potentials[i] == INF) 
                    continue;

                for (auto &e : edges[i]) {

                    if ((e.capacity > 0) and ((potentials[i] + e.cost) < potentials[e.to])) {

                        potentials[e.to] = potentials[i] + e.cost;
                        changed = 1;
                    }
                }
            }
        }

        assert(it >= 0); 
        return;
    }
};

void runTestCases() {

    
    return;
}

signed main() {

    ios_base::sync_with_stdio(false);
    cin.tie(nullptr);

    int T = 1;
    // cin >> T;

    while (T--) 
        runTestCases();

    return 0;

}
