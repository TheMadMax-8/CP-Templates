#include<bits/stdc++.h>
#include<atcoder/all>

using namespace std;
using namespace atcoder;

using i64 = long long;
using Pair = array<i64, 2>;
using grid = vector<vector<i64>>;

using BIT = fenwick_tree<i64>;
using Z = modint998244353;

using u64 = unsigned long long;

vector<Z> factorial;
vector<Z> inverseFactorial;
vector<Z> powers2;

const int mod1 = 1e9 + 7;
const int mod2 = 998244353;
const int mod3 = 676767677;

const int maxN = 2e5 + 42;

void preComputeFactorialsAndInverseFactorials() {

    factorial.resize(maxN + 1);
    inverseFactorial.resize(maxN + 1);

    factorial[0] = 1;

    for (int i = 1; i <= maxN; ++i)
        factorial[i] = factorial[i - 1] * i;

    inverseFactorial[maxN] = factorial[maxN].inv();

    for (int i = maxN - 1; i >= 0; --i) 
        inverseFactorial[i] = inverseFactorial[i + 1] * (i + 1);

    return;
}

Z ncr(i64 N, i64 R) {

    if ((R < 0) or (R > N))
        return (Z) 0LL;

    Z ans = factorial[N] * inverseFactorial[R] * inverseFactorial[N - R];
    return ans;
}

void runTestCases() {

    
    return;
}

signed main() {

    ios_base::sync_with_stdio(false);
    cin.tie(nullptr);

    int T = 1;
    // cin >> T;

    // preComputeFactorialsAndInverseFactorials();

    while (T-- > 0) 
        runTestCases();

    return 0;
}