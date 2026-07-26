#include<bits/stdc++.h>
using namespace std;

#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>
 
using namespace __gnu_pbds;
 
template<typename T>
using increasing_ordered_set = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;

template<typename T>
using decreasing_ordered_set = tree<T, null_type, greater<T>, rb_tree_tag, tree_order_statistics_node_update>;

template<typename T>
using increasing_ordered_multiset = tree<T, null_type, less_equal<T>, rb_tree_tag, tree_order_statistics_node_update>;

template<typename T>
using decreasing_ordered_multiset = tree<T, null_type, greater_equal<T>, rb_tree_tag, tree_order_statistics_node_update>;

using i64 = long long;
using u32 = unsigned int;
using u64 = unsigned long long;

using u128 = unsigned __int128;
using i128 = __int128;

using Pair = array<i64, 2>;
using grid = vector<vector<i64>>;

// I Have Used Jiangly's Template.

template<class T>
constexpr T power(T a, i64 b) {

    T ans {1};

    while (b != 0) {

        if ((b & 1) != 0)
            ans *= a;

        b >>= 1LL;
        a *= a;
    }

    return ans;
}

template<u32 P>
constexpr u32 multiply(u32 a, u32 b) {

    u32 ans = u64(a) * b % P;
    return ans;
}
 
template<u64 P>
constexpr u64 multiply(u64 a, u64 b) {

    u64 ans = a * b - u64(1.L * a * b / P - 0.5L) * P;
    ans %= P;

    return ans;
}
 
constexpr i64 safeMod(i64 x, i64 m) {

    x %= m;

    if (x < 0) 
        x += m;

    return x;
}
 
constexpr Pair extended_euclideanGCD(i64 a, i64 b) {

    a = safeMod(a, b);

    if (a == 0)
        return {b, 0};
    
    i64 s1 = b, s2 = a;
    i64 m0 = 0, m1 = 1;
 
    while (s2 != 0) {

        i64 u = s1 / s2;

        s1 -= s2 * u;
        m0 -= m1 * u;
        
        swap(s1, s2);
        swap(m0, m1);
    }
    
    if (m0 < 0)
        m0 += b / s1;
    
    return {s1, m0};
}
 
template<std::unsigned_integral U, U P>

struct ModIntBase {
public:
    constexpr ModIntBase() : x(0) {}
    template<std::unsigned_integral T>

    constexpr ModIntBase(T x_) : x(x_ % mod()) {}
    template<std::signed_integral T>

    constexpr ModIntBase(T x_) {

        using S = make_signed_t<U>;
        S p = x_ % S(mod());

        if (p < 0) 
            p += mod();

        x = p;
    }
    
    constexpr static U mod() {
        return P;
    }
    
    constexpr U value() const {
        return x;
    }
    
    constexpr ModIntBase operator-() const {

        ModIntBase ans;
        ans.x = (x == 0 ? 0 : mod() - x);

        return ans;
    }
    
    constexpr ModIntBase inverse() const {

        auto G = extended_euclideanGCD(x, mod());
        // assert(G[0] == 1);

        return G[1];
    }
    
    constexpr ModIntBase &operator *= (const ModIntBase &RHS) & {

        x = multiply<mod()>(x, RHS.value());
        return *this;
    }

    constexpr ModIntBase &operator += (const ModIntBase &RHS) & {

        x += RHS.value();

        if (x >= mod()) 
            x -= mod();
        
        return *this;
    }

    constexpr ModIntBase &operator -= (const ModIntBase &RHS) & {

        x -= RHS.value();

        if (x >= mod()) 
            x += mod();
        
        return *this;
    }

    constexpr ModIntBase &operator /= (const ModIntBase &RHS) & {
        return *this *= RHS.inverse();
    }
    
    friend constexpr ModIntBase operator * (ModIntBase LHS, const ModIntBase &RHS) {

        LHS *= RHS;
        return LHS;
    }

    friend constexpr ModIntBase operator + (ModIntBase LHS, const ModIntBase &RHS) {

        LHS += RHS;
        return LHS;
    }

    friend constexpr ModIntBase operator - (ModIntBase LHS, const ModIntBase &RHS) {

        LHS -= RHS;
        return LHS;
    }

    friend constexpr ModIntBase operator / (ModIntBase LHS, const ModIntBase &RHS) {

        LHS /= RHS;
        return LHS;
    }
    
    friend constexpr std::istream &operator >> (std::istream &inS, ModIntBase &a) {

        i64 i;
        inS >> i;

        a = i;
        return inS;
    }

    friend constexpr std::ostream &operator << (std::ostream &outS, const ModIntBase &a) {
        return outS << a.value();
    }
    
    friend constexpr bool operator == (const ModIntBase &LHS, const ModIntBase &RHS) {
        return LHS.value() == RHS.value();
    }

    friend constexpr std::strong_ordering operator <=> (const ModIntBase &LHS, const ModIntBase &RHS) {
        return LHS.value() <=> RHS.value();
    }
    
private:
    U x;
};
 
template<u32 P>
using ModInt = ModIntBase<u32, P>;

template<u64 P>
using ModInt64 = ModIntBase<u64, P>;
 
struct Barrett {
public:
    Barrett(u32 mod_) : Mod(mod_), inverse_mod((u64)(-1) / mod_ + 1) {}
 
    constexpr u32 mod() const {
        return Mod;
    }
 
    constexpr u32 multiply(u32 a, u32 b) const {

        u64 z = a;
        z *= b;
        
        u64 x = u64((u128(z) * inverse_mod) >> 64);
        u32 v = u32(z - x * Mod);

        if (Mod <= v) 
            v += Mod;
        
        return v;
    }
 
private:

    u32 Mod;
    u64 inverse_mod;
};
 
template<u32 Id>

struct DynamicModInt {
public:
    constexpr DynamicModInt() : x(0) {}
    template<std::unsigned_integral T>

    constexpr DynamicModInt(T x_) : x(x_ % mod()) {}
    template<std::signed_integral T>

    constexpr DynamicModInt(T x_) {

        int v = x_ % int(mod());

        if (v < 0) 
            v += mod();

        x = v;
    }
    
    constexpr static void setMod(u32 m) {
        Barrett_DynamicT = m;
    }
    
    static u32 mod() {
        return Barrett_DynamicT.mod();
    }
    
    constexpr u32 value() const {
        return x;
    }
    
    constexpr DynamicModInt operator - () const {

        DynamicModInt ans;
        ans.x = (x == 0 ? 0 : mod() - x);
        return ans;
    }
    
    constexpr DynamicModInt inverse() const {

        auto G = extended_euclideanGCD(x, mod());
        assert(G[0] == 1);

        return G[1];
    }
    
    constexpr DynamicModInt &operator *= (const DynamicModInt &RHS) & {

        x = Barrett_DynamicT.multiply(x, RHS.value());
        return *this;
    }

    constexpr DynamicModInt &operator += (const DynamicModInt &RHS) & {

        x += RHS.value();

        if (x >= mod()) 
            x -= mod();
        
        return *this;
    }

    constexpr DynamicModInt &operator -= (const DynamicModInt &RHS) & {

        x -= RHS.value();

        if (x >= mod()) 
            x += mod();
        
        return *this;
    }

    constexpr DynamicModInt &operator /= (const DynamicModInt &RHS) & {
        return *this *= RHS.inverse();
    }
    
    friend constexpr DynamicModInt operator * (DynamicModInt LHS, const DynamicModInt &RHS) {

        LHS *= RHS;
        return LHS;
    }

    friend constexpr DynamicModInt operator + (DynamicModInt LHS, const DynamicModInt &RHS) {

        LHS += RHS;
        return LHS;
    }

    friend constexpr DynamicModInt operator - (DynamicModInt LHS, const DynamicModInt &RHS) {

        LHS -= RHS;
        return LHS;
    }

    friend constexpr DynamicModInt operator / (DynamicModInt LHS, const DynamicModInt &RHS) {

        LHS /= RHS;
        return LHS;
    }
    
    friend constexpr std::istream &operator >> (std::istream &inS, DynamicModInt &a) {

        i64 i;
        inS >> i;

        a = i;
        return inS;
    }

    friend constexpr std::ostream &operator << (std::ostream &outS, const DynamicModInt &a) {
        return outS << a.value();
    }
    
    friend constexpr bool operator == (const DynamicModInt &LHS, const DynamicModInt &RHS) {
        return LHS.value() == RHS.value();
    }

    friend constexpr std::strong_ordering operator <=> (const DynamicModInt &LHS, const DynamicModInt &RHS) {
        return LHS.value() <=> RHS.value();
    }
    
private:
    u32 x;
    static Barrett Barrett_DynamicT;
};
 
template<u32 Id>
Barrett DynamicModInt<Id>::Barrett_DynamicT = 998244353;
 
using Z = ModInt<998244353>;
 
struct Combinatorics {

    int N;
    std::vector<Z> _Factorials;
    std::vector<Z> _inverseFactorials;
    std::vector<Z> _inverse;
    
    Combinatorics() : N{0}, _Factorials{1}, _inverseFactorials{1}, _inverse{0} {}

    Combinatorics(int N) : Combinatorics() {
        initialise(N);
    }
    
    void initialise(int maxN) {

        if (maxN <= N) 
            return;
            
        _Factorials.resize(maxN + 1);
        _inverseFactorials.resize(maxN + 1);
        _inverse.resize(maxN + 1);
        
        for (int i = N + 1; i <= maxN; i++) 
            _Factorials[i] = _Factorials[i - 1] * i;

        _inverseFactorials[maxN] = _Factorials[maxN].inverse();

        for (int i = maxN; i > N; i--) {

            _inverseFactorials[i - 1] = _inverseFactorials[i] * i;
            _inverse[i] = _inverseFactorials[i] * _Factorials[i - 1];
        }

        N = maxN;
        return;
    }
    
    Z Factorials(int maxN) {

        if (maxN > N) 
            initialise(2 * maxN);

        return _Factorials[maxN];
    }

    Z inverseFactorials(int maxN) {

        if (maxN > N) 
            initialise(2 * maxN);

        return _inverseFactorials[maxN];
    }

    Z inverse(int maxN) {

        if (maxN > N) 
            initialise(2 * maxN);

        return _inverse[maxN];
    }

    Z ncr(int N, int R) {

        if ((N < R) or (R < 0))
            return 0;

        return Factorials(N) * inverseFactorials(R) * inverseFactorials(N - R);
    }

} Combinatorics;

constexpr int P = Z::mod();
constexpr int root = 62;

// Satyam343's Template NTT.
// Adapted His Implementation (https://codeforces.com/contest/2169/submission/348974916).

void NTT(vector<Z> &A) {
    
    int N = A.size();
    int msb = 63 - __builtin_clzll(N);
    
    vector<Z> roots_unity (N, 1);
    vector<int> reverse_bit (N);
    
    for (int k = 2, s = 2; k < N; k *= 2, ++s) {
        
        Z x[2] = {1, power(Z(root), (P - 1) >> s)};
        
        for (int i = k; i < k * 2; ++i)
            roots_unity[i] = roots_unity[i / 2] * x[i % 2];
    }
    
    for (int i = 0; i < N; ++i) 
        reverse_bit[i] = (reverse_bit[i / 2] | (i % 2) << msb) / 2;
        
    for (int i = 0; i < N; ++i) {
        
        if (i < reverse_bit[i])
            swap(A[i], A[reverse_bit[i]]);
    }
    
    for (int k = 1; k < N; k *= 2) {
        
        for (int i = 0; i < N; i += k * 2) {
            
            for (int j = 0; j < k; ++j) {
                
                Z x = roots_unity[j + k] * A[i + j + k];
                
                A[i + j + k] = A[i + j] - x;
                A[i + j] += x;
            }
        }
    }
    
    return;
}

vector<Z> convolute(vector<Z> &A, vector<Z> &B) {
    
    if ((A.empty() == 1) or (B.empty() == 1))
        return {};
        
    vector<Z> ans;
    
    int s = A.size() + B.size() - 1;
    int msb = 64 - __builtin_clzll(s);
    
    int N = 1 << msb;
    vector<Z> L (A), R (B);
    
    ans.resize(N);
    L.resize(N);
    R.resize(N);
    
    NTT(L);
    NTT(R);
    
    for (int i = 0; i < N; ++i)
        ans[-i & (N - 1)] = L[i] * R[i] / N;
        
    NTT(ans);
    
    ans.resize(s);
    return ans;
}

vector<vector<Z>> Multiply(vector<vector<Z>> &A, vector<vector<Z>> &B) {
 
    int N = A.size();
 
    int B1 = B.size();
    int B2 = B[0].size();
    
    vector<vector<Z>> ans (N, vector<Z> (B2, 0));
 
    for (int i = 0; i < N; ++i) {
 
        for (int k = 0; k < B1; ++k) {
 
            if (A[i][k] == 0)
                continue;
 
            for (int j = 0; j < B2; ++j)
                ans[i][j] += (A[i][k] * B[k][j]);
        }
    }
 
    return ans;
}
 
vector<vector<Z>> Exponent(vector<vector<Z>> base, i64 p) {
 
    int N = base.size();
    vector<vector<Z>> ans (N, vector<Z> (N, 0));
 
    for (int i = 0; i < N; ++i)
        ans[i][i] = 1LL;
 
    while (p != 0) {
 
        if ((p & 1) != 0)
            ans = Multiply(ans, base); // Odd Power.
 
        base = Multiply(base, base);
        p >>= 1;
    }

    return ans;
}
 
vector<Z> rowByMatrix(vector<Z> &A, vector<vector<Z>> &M) {
 
    int N = A.size();
    
    assert(N == M.size());
    assert(N == M[0].size());
 
    vector<Z> ans (N, 0);
 
    for (int i = 0; i < N; ++i) {
 
        if (A[i] == 0)
            continue;
 
        for (int j = 0; j < N; ++j)
            ans[j] += A[i] * M[i][j];
    }
 
    return ans;
}

template<typename T>
struct FenwickTree {

    int N;
    std::vector<T> A;
    
    FenwickTree(int N_ = 0) {
        initialise(N_);
    }
    
    void initialise(int N_) {

        N = N_;
        A.assign(N, T{});
        return;
    }
    
    void update(int index, const T &x) {

        for (int i = index + 1; i <= N; i += (i & -i))
            A[i - 1] = A[i - 1] + x;

        return;
    }
    
    T sum(int index) {

        T ans{};

        for (int i = index; i >= 1; i -= (i & -i)) 
            ans = ans + A[i - 1];
        
        return ans;
    }
    
    T rangeSum(int L, int R) {
        
        T ans = sum(R) - sum(L);
        return ans;
    } 
    
    int select(const T &k) {

        int x = 0, i = 1 << std::__lg(N);
        T current{};

        while (i != 0) {

            if ((x + i > N) or (current + A[x + i - 1] > k)) {

                i >>= 1;
                continue;
            }

            x += i;
            current += A[x - 1];

            i >>= 1;
        }

        return x;
    }
};

template<class Info>
struct SegmentTree {

    int N;
    std::vector<Info> info;

    SegmentTree() : N(0) {}

    SegmentTree(int N_, Info V_ = Info()) {
        initialise(N_, V_);
    }

    template<class T>
    SegmentTree(std::vector<T> initialise_) {
        initialise(initialise_);
    }

    void initialise(int N_, Info V_ = Info()) {
        initialise(std::vector(N_, V_));
    }

    template<class T>
    void initialise(std::vector<T> initialise_) {

        N = initialise_.size();
        info.assign(4 << std::__lg(N), Info());

        std::function<void(int, int, int)> build = [&](int node, int L, int R) {

            if (R - L == 1) {

                info[node] = initialise_[L];
                return;
            }

            int mid = L + (R - L) / 2;

            build(2 * node, L, mid);
            build(2 * node + 1, mid, R);

            pull(node);
            return;
        };

        build(1, 0, N);
        return;
    }

    void pull(int node) {

        info[node] = info[2 * node] + info[2 * node + 1];
        return;
    }

    void update(int node, int L, int R, int x, const Info &V) {

        if (R - L == 1) {

            info[node] = V;
            return;
        }

        int mid = L + (R - L) / 2;

        if (x < mid) 
            update(2 * node, L, mid, x, V);

        else
            update(2 * node + 1, mid, R, x, V);
    
        pull(node);
        return;
    }

    void update(int node, const Info &V) {

        update(1, 0, N, node, V);
        return;
    }

    Info rangeQuery(int node, int L, int R, int i, int j) {

        if (L >= j || R <= i) 
            return Info();

        if (L >= i && R <= j) 
            return info[node];

        int mid = L + (R - L) / 2;
        return rangeQuery(2 * node, L, mid, i, j) + rangeQuery(2 * node + 1, mid, R, i, j);
    }

    Info rangeQuery(int L, int R) {
        return rangeQuery(1, 0, N, L, R);
    }

    template<class F>
    int findFirst(int node, int L, int R, int i, int j, F &&A) {

        if (L >= j || R <= i) 
            return -1;
        
        if (L >= i && R <= j && (A(info[node]) == 0)) 
            return -1;
        
        if (R - L == 1) 
            return L;
        
        int mid = L + (R - L) / 2;
        int ans = findFirst(2 * node, L, mid, i, j, A);

        if (ans == -1) 
            ans = findFirst(2 * node + 1, mid, R, i, j, A);
        
        return ans;
    }

    template<class F>
    int findFirst(int L, int R, F &&A) {
        return findFirst(1, 0, N, L, R, A);
    }

    template<class F>
    int findLast(int node, int L, int R, int i, int j, F &&A) {

        if (L >= j || R <= i) 
            return -1;
        
        if (L >= i && R <= j && (A(info[node]) == 0)) 
            return -1;
        
        if (R - L == 1) 
            return L;
        
        int mid = L + (R - L) / 2;
        int ans = findLast(2 * node + 1, mid, R, i, j, A);

        if (ans == -1) 
            ans = findLast(2 * node, L, mid, i, j, A);

        return ans;
    }

    template<class F>
    int findLast(int L, int R, F &&A) {
        return findLast(1, 0, N, L, R, A);
    }
};

const int INF = 1e9;
 
struct Info {
    int mini = INF;
};
 
Info operator + (const Info &A, const Info &B) {
    return {std::min(A.mini, B.mini)};
}

class DisjointSet {
public:
    vector<int> size, parent, rank;

    DisjointSet(int N) {

        size.resize(N + 1, 1);
        rank.resize(N + 1, 0);
        
        parent.resize(N + 1);
        iota(parent.begin(), parent.end(), 0);
    }
    
    int findParent(int u) {
        
        // Recursive Call.
        // Path Compression.

        if (parent[u] != u) 
            parent[u] = findParent(parent[u]);
        
        return parent[u];
    }

    // Returns Size Of Parent Node.
    
    int findSize(int u) {
        return size[findParent(u)];
    }

    // Connect Smaller Component To Larger Component.
    // This Reduces Height Of Component (Path Compression) And Minimise Discovery Time Of Parent Node.

    void UnionBySize(int u, int v) {
        
        int uParent = findParent(u);
        int vParent = findParent(v);
        
        if (uParent == vParent) 
            return;
        
        if (size[uParent] >= size[vParent]) {
            
            parent[vParent] = uParent;
            size[uParent] += size[vParent];
        }
        
        else {
            
            parent[uParent] = vParent;
            size[vParent] += size[uParent];
        }
    }
    
    void UnionByRank(int u, int v) {
        
        int uParent = findParent(u);
        int vParent = findParent(v);
        
        if (uParent == vParent) 
            return;
        
        if (rank[uParent] == rank[vParent]) {
            
            parent[vParent] = uParent;
            ++rank[uParent];
        }
        
        else if (rank[uParent] > rank[vParent]) 
            parent[vParent] = uParent;          

        else 
            parent[uParent] = vParent;
    }

    bool isConnected(int u, int v) {
        return (findParent(u) == findParent(v));
    }

    int countComponents() {

        int ans = 0;

        for (int i = 0; i < parent.size(); ++i)
            ans += (parent[i] == i);

        // For 'N' Nodes, We Are Considering N + 1 Independent Components.
        // So After All Connections, One Component Will Be Counted Extra.

        return ans - 1; 
    }

    void reset(int node) {

        parent[node] = node;
        return;
    }

    // A Special Function To Do Union By Lexicography.
    // Same Logic As We Do Union By Size Or Rank.
    // Just Reverse Order :- Lexicographically Smaller Character Is Parent.

    void UnionByLexicography(int u, int v) {

        int uParent = findParent(u);
        int vParent = findParent(v);

        if (uParent == vParent)
            return; // Already Belongs To The Same Component.

        else if (uParent > vParent)
            parent[uParent] = vParent;

        else
            parent[vParent] = uParent;

        return;
    }

    bool Unite(int u, int v) {

        u = findParent(u);
        v = findParent(v);

        if (u == v)
            return false;

        if (size[u] < size[v])
            swap(u, v);

        parent[v] = u;
        size[u] += size[v];

        return true;
    }
};

// template<class Info, class Tag>
// struct LazySegmentTree {

//     int N;
//     std::vector<Info> info;
//     std::vector<Tag> tag;

//     LazySegmentTree() : N(0) {}

//     LazySegmentTree(int N_, Info V_ = Info()) {
//         initialise(N_, V_);
//     }

//     template<class T>
//     LazySegmentTree(std::vector<T> initialise_) {
//         initialise(initialise_);
//     }

//     void initialise(int N_, Info V_ = Info()) {
//         initialise(std::vector(N_, V_));
//     }

//     template<class T>
//     void initialise(std::vector<T> initialise_) {

//         N = initialise_.size();

//         info.assign(4 << std::__lg(N), Info());
//         tag.assign(4 << std::__lg(N), Tag());

//         std::function<void(int, int, int)> build = [&](int node, int L, int R) {

//             if (R - L == 1) {

//                 info[node] = initialise_[L];
//                 return;
//             }

//             int mid = L + (R - L) / 2;

//             build(2 * node, L, mid);
//             build(2 * node + 1, mid, R);

//             pull(node);
//             return;
//         };

//         build(1, 0, N);
//         return;
//     }

//     void pull(int node) {

//         info[node] = info[2 * node] + info[2 * node + 1];
//         return;
//     }

//     void apply(int node, const Tag &V) {

//         info[node].apply(V);
//         tag[node].apply(V);

//         return;
//     }

//     void push(int node) {

//         apply(2 * node, tag[node]);
//         apply(2 * node + 1, tag[node]);

//         tag[node] = Tag();
//         return;
//     }

//     void update(int node, int L, int R, int x, const Info &V) {

//         if (R - L == 1) {

//             info[node] = V;
//             return;
//         }

//         int mid = L + (R - L) / 2;
//         push(node);

//         if (x < mid) 
//             update(2 * node, L, mid, x, V);

//         else
//             update(2 * node + 1, mid, R, x, V);
    
//         pull(node);
//         return;
//     }

//     void update(int node, const Info &V) {

//         update(1, 0, N, node, V);
//         return;
//     }

//     Info rangeQuery(int node, int L, int R, int i, int j) {

//         if (L >= j || R <= i) 
//             return Info();

//         if (L >= i && R <= j) 
//             return info[node];

//         int mid = L + (R - L) / 2;
//         push(node);

//         return rangeQuery(2 * node, L, mid, i, j) + rangeQuery(2 * node + 1, mid, R, i, j);
//     }

//     Info rangeQuery(int L, int R) {
//         return rangeQuery(1, 0, N, L, R);
//     }

//     void rangeApply(int node, int L, int R, int i, int j, const Tag &V) {

//         if (L >= j || R <= i) 
//             return;
        
//         if (L >= i && R <= j) {

//             apply(node, V);
//             return;
//         }

//         int mid = (L + R) / 2;
//         push(node);

//         rangeApply(2 * node, L, mid, i, j, V);
//         rangeApply(2 * node + 1, mid, R, i, j, V);

//         pull(node);
//         return;
//     }

//     void rangeApply(int L, int R, const Tag &V) {
//         return rangeApply(1, 0, N, L, R, V);
//     }

//     template<class F>
//     int findFirst(int node, int L, int R, int i, int j, F &&A) {

//         if (L >= j || R <= i) 
//             return -1;
        
//         if (L >= i && R <= j && (A(info[node]) == 0)) 
//             return -1;
        
//         if (R - L == 1) 
//             return L;
        
//         int mid = L + (R - L) / 2;
//         push(node);

//         int ans = findFirst(2 * node, L, mid, i, j, A);

//         if (ans == -1) 
//             ans = findFirst(2 * node + 1, mid, R, i, j, A);
        
//         return ans;
//     }

//     template<class F>
//     int findFirst(int L, int R, F &&A) {
//         return findFirst(1, 0, N, L, R, A);
//     }

//     template<class F>
//     int findLast(int node, int L, int R, int i, int j, F &&A) {

//         if (L >= j || R <= i) 
//             return -1;
        
//         if (L >= i && R <= j && (A(info[node]) == 0)) 
//             return -1;
        
//         if (R - L == 1) 
//             return L;
        
//         int mid = L + (R - L) / 2;
//         push(node);

//         int ans = findLast(2 * node + 1, mid, R, i, j, A);

//         if (ans == -1) 
//             ans = findLast(2 * node, L, mid, i, j, A);

//         return ans;
//     }

//     template<class F>
//     int findLast(int L, int R, F &&A) {
//         return findLast(1, 0, N, L, R, A);
//     }
// };
 
// const int INF = 1e9;

// struct Tag {

//     int add = 0;

//     void apply(const Tag &T) {

//         add += T.add;
//         return;
//     }
// };
 
// struct Info {

//     int mini = INF;

//     void apply(const Tag &T) {

//         mini += T.add;
//         return;
//     }
// };
 
// Info operator + (const Info &A, const Info &B) {
//     return {std::min(A.mini, B.mini)};
// }

using Z1 = ModInt<1000000007>;
using Z2 = ModInt<998244353>;

mt19937_64 randomGenerator(chrono::steady_clock::now().time_since_epoch().count());

u32 get_random_base(u32 mini, u32 maxi) {

    u32 base = uniform_int_distribution<u32>(mini, maxi)(randomGenerator);
    return base;
}

class Hashing {
private:
    int N;
    string S;
    
    vector<Z1> powers1, prefix1;
    vector<Z2> powers2, prefix2;
    
    const Z1 prime1 = get_random_base(300, 1000) ^ 1;
    const Z2 prime2 = get_random_base(1000, 2000) ^ 1;

public:  
    void initialise(const string &s) {
        
        S = s;
        N = s.size();
        
        powers1.assign(N + 5, 1);
        powers2.assign(N + 5, 1);

        prefix1.assign(N + 5, 0);
        prefix2.assign(N + 5, 0);
        
        for (int i = 1; i <= N; ++i) {
            
            powers1[i] = powers1[i - 1] * prime1; 
            powers2[i] = powers2[i - 1] * prime2; 
        }
        
        for (int i = 1; i <= N; ++i) {
            
            prefix1[i] = prefix1[i - 1] * prime1 + int(S[i - 1] - 'a' + 1);
            prefix2[i] = prefix2[i - 1] * prime2 + int(S[i - 1] - 'a' + 1);
        }
        
        return;
    }
    
    array<u32, 2> get_hash(int L, int R) {
        
        int size = R - L + 1;
        
        Z1 hash1 = prefix1[R] - prefix1[L - 1] * powers1[size];
        Z2 hash2 = prefix2[R] - prefix2[L - 1] * powers2[size];
        
        return {hash1.value(), hash2.value()};
    }
    
    bool is_greater(int i1, int j1, int i2, int j2) {
        
        int size1 = j1 - i1 + 1;
        int size2 = j2 - i2 + 1;
        
        int low = 1;
        int high = min(size1, size2);
        
        int lowest_common_prefix = 0;
        
        while (low <= high) {
            
            int mid = low + (high - low) / 2;
            
            if (get_hash(i1, i1 + mid - 1) == get_hash(i2, i2 + mid - 1)) {
                
                lowest_common_prefix = mid;
                low = mid + 1;
            }
            
            else
                high = mid - 1;
        }
        
        if (lowest_common_prefix == min(size1, size2))
            return size1 > size2;
            
        return S[i1 + lowest_common_prefix - 1] > S[i2 + lowest_common_prefix - 1];
    }
};

// Aho - Corasick Trie.
// Thanks To CP Algorithms Blog.

struct Node {

    i64 next[26];
    i64 go[26];

    i64 out = 0;
    i64 p = -1, link = -1;

    char ch;

    Node(i64 p = -1, char ch = '$') : p (p), ch (ch) {

        fill(next, next + 26, -1);
        fill(go, go + 26, -1);
    }
};

vector<Node> Trie (1);
int linked = 0;

void insert(const string &s, i64 index) {

    i64 x = 0;

    for (auto &c : s) {

        if (Trie[x].next[c - 'a'] == -1) {

            Trie[x].next[c - 'a'] = (i64) Trie.size();
            Trie.emplace_back(x, c);
        }

        x = Trie[x].next[c - 'a'];
    }

    Trie[x].out |= (1LL << index);
    return;
}

void buildLinks() {

    if (linked == 1)
        return;
    
    queue<i64> q;
    Trie[0].link = 0;

    for (int c = 0; c < 26; ++c) {

        if (Trie[0].next[c] != -1) {

            i64 node = Trie[0].next[c];
            Trie[0].go[c] = node;

            Trie[node].link = 0;
            q.push(node);
        }

        else    
            Trie[0].go[c] = 0;
    } 

    while (q.empty() == false) {

        auto node = q.front();
        q.pop();

        for (int c = 0; c < 26; ++c) {

            if (Trie[node].next[c] != -1) {

                i64 child = Trie[node].next[c];
                Trie[child].link = Trie[Trie[node].link].go[c];

                Trie[child].out |= Trie[Trie[child].link].out;
                Trie[node].go[c] = child;

                q.push(child);
            }
    
            else    
                Trie[node].go[c] = Trie[Trie[node].link].go[c];
        } 
    }

    linked = 1;
    return;
}
 

i64 forward(i64 x, char c) {

    if (linked == 0)
        buildLinks();

    return Trie[x].go[c - 'a'];
}

i64 accessLink(i64 x) {

    if (linked == 0)
        buildLinks();

    return Trie[x].link;
}

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

const int maxN = 2e6 + 42;

// MCMF Theorem.
// USACO Guide (KACTL's Implementation) + CP Algorithms.

struct Edge {

    int from, to, reversed;
    i64 capacity, cost, flow;
};

struct MCMF {

    int N;

    vector<vector<Edge>> edges;
    vector<int> seen, parent_node, parent_edge;
    vector<i64> distances, potentials;
    vector<Edge*> parents;

    MCMF(int N) : N (N), edges (N), seen (N), distances (N), potentials (N), parents (N), parent_node (N), parent_edge (N) {}

    void addEdge(int from, int to, i64 capacity, i64 cost) {

        if (from == to)
            return;

        edges[from].push_back(Edge {from, to, (int) edges[to].size(), capacity, cost, 0});
        edges[to].push_back(Edge {to, from, (int) edges[from].size() - 1, 0, -cost, 0});

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

        i64 netFlow = 0;
        i64 netCost = 0;

        while ((path_CP(source, sink) == 1) and (distances[sink] < 0)) {
         
            i64 push = INF;
            int current = sink;

            while (current != source) {

                int parent = parent_node[current];
                int index = parent_edge[current];

                push = min(push, edges[parent][index].capacity - edges[parent][index].flow);
                current = parent;
            }

            netFlow += push;
            netCost += push * distances[sink];
            
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

        return {netFlow, netCost};
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

        i64 netFlow = 0;
        i64 netCost = 0;

        while (path(source), seen[sink]) {

            i64 push = INF;
            
            for (Edge* x = parents[sink]; x != 0; x = parents[x -> from])
                push = min(push, x -> capacity - x -> flow);

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

struct Edge_Biconnected_Components {

    int N;
    int current, count;
    
    std::vector<std::vector<int>> adj;
    std::vector<int> stack;
    std::vector<int> discovery, low, component;
    
    Edge_Biconnected_Components() {}

    Edge_Biconnected_Components(int N) {
        initialise(N);
    }
    
    void initialise(int N) {

        this -> N = N;
        adj.assign(N, {});

        discovery.assign(N, -1);
        low.resize(N);
        component.assign(N, -1);

        stack.clear();
        current = count = 0;

        return;
    }
    
    void addEdge(int u, int v) {

        adj[u].push_back(v);
        adj[v].push_back(u);
    }
    
    void dfs(int node, int p) {

        discovery[node] = low[node] = current++;
        stack.push_back(node);
        
        for (auto child : adj[node]) {

            if (child == p) 
                continue;
            
            if (discovery[child] == -1) {

                dfs(child, node);
                low[node] = std::min(low[node], low[child]);
            } 
            
            else if (component[child] == -1) 
                low[node] = std::min(low[node], discovery[child]);
        }
        
        if (discovery[node] == low[node]) {

            int current;

            do {

                current = stack.back();
                component[current] = count;
                stack.pop_back();

            } while (current != node);

            count++;
        }
    }
    
    std::vector<int> work() {

        for (int i = 0; i < N; i++) {

            if (discovery[i] == -1) 
                dfs(i, -1);
        }

        return component;
    }
    
    struct Graph {

        int N;

        std::vector<pair<int, int>> edges;
        std::vector<int> sizes;
        std::vector<int> count_edges;
    };

    Graph compress() {

        Graph G;

        G.N = count;
        G.sizes.resize(count);
        G.count_edges.resize(count);

        for (int i = 0; i < N; i++) {

            G.sizes[component[i]]++;

            for (auto j : adj[i]) {

                if (component[i] < component[j]) 
                    G.edges.emplace_back(component[i], component[j]);  

                else if (i < j) 
                    G.count_edges[component[i]]++;
            }
        }

        return G;
    }
};

struct custom_hash {
 
    static uint64_t splitmix64(uint64_t x) {
        
        x += 0x9e3779b97f4a7c15;
        x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9;
        x = (x ^ (x >> 27)) * 0x94d049bb133111eb;
        return x ^ (x >> 31);
    }
 
    size_t operator()(uint64_t x) const {
 
        static const uint64_t FIXED_RANDOM = chrono::steady_clock::now().time_since_epoch().count();
        return splitmix64(x + FIXED_RANDOM);
    }
};

vector<int> SPF;
vector<bool> is_prime;

using Triplet = array<i64, 3>;

void sieve() {

    SPF.resize(maxN + 1);
    is_prime.assign(maxN + 1, true);

    iota(SPF.begin(), SPF.end(), 0);
    is_prime[0] = is_prime[1] = 0;

    for (int i = 2; i * i <= maxN; ++i) {

        if (is_prime[i] == 0)
            continue;

        for (int j = i * i; j <= maxN; j += i) {

            is_prime[j] = 0;

            if (SPF[j] == j)
                SPF[j] = i;
        }
    }

    return;
}

void runTestCases() {
    
    
    return;
}

signed main() {

    ios_base::sync_with_stdio(false);
    cin.tie(nullptr);

    int T = 1;
    cin >> T;

    // sieve();

    while (T-- > 0) 
        runTestCases();

    return 0;
}