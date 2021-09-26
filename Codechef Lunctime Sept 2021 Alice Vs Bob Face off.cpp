#include <bits/stdc++.h>
using namespace std;

#define ll long long int

#define vi vector<int>
#define vli vector<ll>
#define vc vector<char>
#define vb vector<bool>
#define vs vector<string>
#define pii pair<int,int>
#define plili pair<ll,ll>


#define pb push_back
#define pp pop_back
#define sz(a) a.size()
#define sortv(a) sort(a.begin(),a.end())
#define sortr(a) sort(a.rbegin(), a.rend())
#define all(a) a.begin(), a.end()
#define nline "\n"

const int mod = 1e9 + 7;
const int MOD = 1e9 + 7;
const ll inf = LLONG_MAX;
const int sz = 1e5 + 5;
const unsigned ll inff = ULLONG_MAX;


void db(pii &a){
  cerr << a.first << " " << a.second << " ";
}
ll lcm(ll a, ll b)
{
    return (a * 1LL * b)/__gcd(a,b);
}


// bool comp(pair<int,int> a, pair<int,int> b)
// {
//   return a.first > b.first;
// }

bool sq(int n)
{
  if((int)sqrt(n)*(int)sqrt(n) == n)
   return 1;
 else
  return 0;
}
 
const int N = 1e5 + 5;
vector<int> adj[4 * N];

vector<bool>visited(4 * N,0);
ll expo(ll a, ll b)
{
  if(b == 0)
    return 1;
  if(b == 1)
    return a;
  
  ll ans =  expo(a, b / 2);
  ans = ans * 1LL * ans;
  if(b & 1)
    ans *= a;
  return ans;

}

const int maxSize = 1e7 + 5;
bool isPrime[N];

void sieveOfEratosthenes(int n)
{
  
  isPrime[0] = isPrime[1] = false;
  for (ll i = 2; i * i < n; i++) {
    if (isPrime[i]) {
        for (ll j = i * i; j < n; j += i)
            isPrime[j] = false;
    }
}
}

bool checkPrime(ll n)
{
  if(n == 1)
    return false;

  for(int i = 2; i * i <= n; i++)
  {
    if(n % i == 0)
      return false;
  }
  return true;
}


bool sign(int n)
{
   return n < 0;
}
// Note: (while debugging) -> do make sure to check for n = 1 and some other smaller number
// -> check for integer overflows
// -> look for some edge cases
// -> Read constraints carefully 

// Way to Proceed: 
// if A or B -> think of brute force solution first, highly probable it will work
// else ->
// 1. DP | dfs or recursion | Observation | 
// 2. BS, greedy (Priority based) -> sets / priority queue / multiset, primes, prime sieve, bitmasks
// 3. Maths, pattern
// 4. Contribution of each element, see what matters the most and leave the rest.
// 5. Range Query (prefix sum) , two pointers, DSU.

pair<int, int> d[4] = {{-1, 0}, {0, -1}, {0, 1}, {1, 0}};
bool v[101][101];

bool isSafe(int x, int y, int n, int m, int mat[][101])
{
   if(x < 0 || x >= n || y < 0 || y >= m)
    return false;
   if(mat[x][y] == 0 || v[x][y])
    return false;

   return true;
}


char mat[101][101];
bool comp(string &a, string &b)
{ 
  if(a.size() < b.size())
    return true;
  else if(a.size() > b.size())
    return false;

  return a < b;
}

// A function to print all prime
// factors of a given number n
void primeFactors(ll n, map<ll, ll> &mapp)
{
    // Print the number of 2s that divide n
    while (n % 2 == 0)
    {
        mapp[2]++;
        n = n/2;
    }
 
    // n must be odd at this point. So we can skip
    // one element (Note i = i +2)
    for (ll i = 3; i <= sqrt(n); i = i + 2)
    {
        // While i divides n, print i and divide n
        while (n % i == 0)
        {
            mapp[i]++;
            n = n/i;
        }
    }
 
    if (n > 2)
        mapp[n]++;
}

ll expoMod(ll a, ll b, ll m) {
    a %= m;
    ll res = 1;

    while (b > 0) {
        if (b & 1)
            res = res * a % m;
        a = a * a % m;
        b >>= 1;
    }

    return res;
}


int countDigits(int n)
{
  int cnt = 0;
  while(n > 0)
  {
     cnt++;
     n = n / 10;
  }
  return cnt;
}

class triplet{
  public: 
  
  int x;
  int y;
  int gcd;
};

triplet extendedEuclid(int a, int b)
{ 
  
  if(b == 0)
  {
     return {1, 0, a};  
  }

  triplet sm = extendedEuclid(b, a % b);
  int x = sm.y;
  int y = sm.x - (a / b) * sm.y;
  return {x, y, sm.gcd};
}

// int mulModInv(int a, int m)
// {
//   // this forms a linear diaphontine equation as a * B + m * Q = 1
//   triplet ans = extendedEuclid(a, m);
//   return ans.x;
// }

 // a^p - a == 0 mod p 
 // a^p = a 
 // a^(p - 1) == 1
 // a ^ -1 = a ^ (p - 2)

ll mulModInv(ll a, ll m)
{
   return expoMod(a, m - 2, m);
}

const int MM = 2e5 + 5;
ll fact[MM];

void computeFact(ll mod)
{
  fact[0] = 1;
  fact[1] = 1;
  for(int i = 2; i < MM; i++)
  {
    fact[i] = (((i % mod) * 1LL *  (fact[i - 1] % mod)) % mod) % mod;
  }

}

ll nCr(ll n, ll r, ll p)
{
    // If n<r, then nCr should return 0
    if (n < r)
        return 0;
    // Base case
    if (r == 0)
        return 1;
 
    // Fill factorial array so that we
    // can find all factorial of r, n
    // and n-r
    // ll fac[n + 1];
    // fac[0] = 1;
    // for (int i = 1; i <= n; i++)
    //     fac[i] = (fac[i - 1] * i) % p;
 
    return (fact[n] * mulModInv(fact[r], p) % p
            * mulModInv(fact[n - r], p) % p)
           % p;
}



// clear thoughts --> cleaner code

struct comparator{
   bool operator()(pii &a, pii &b)
   {
     return a.second > b.second;
   }
};
int computeXOR(int n)
{
   
  // If n is a multiple of 4
  if (n % 4 == 0)
    return n;
 
  // If n%4 gives remainder 1
  if (n % 4 == 1)
    return 1;
 
  // If n%4 gives remainder 2
  if (n % 4 == 2)
    return n + 1;
 
  // If n%4 gives remainder 3
  return 0;
}
bool isSubSequence(string str1, string str2, int m, int n)
{
    int j = 0; // For index of str1 (or subsequence
 
    // Traverse str2 and str1, and
    // compare current character
    // of str2 with first unmatched char
    // of str1, if matched
    // then move ahead in str1
    for (int i = 0; i < n && j < m; i++)
        if (str1[j] == str2[i])
            j++;
 
    // If all characters of str1 were found in str2
    return (j == m);
}

const int M = 998244353;

vector<pii> dir{{-1, 0}, {0, -1}, {0, 1}, {1, 0}, {-1, 1}, {1, -1}, {1, 1}, {-1, -1}};
map<int, set<int>> graph;

ll choose(int n, int r) {
  ll ans = 1;
  for(int i = 0; i < r; i++) {
     ans *= (n - i);
     ans /= (i + 1);
  }
  return ans;
}
// number of elements in [l, r] that give remainder rem when divided by n 
template<class T>
T count(T n, T div, T rem) {
    assert(rem < div);
    return (n + div - rem - 1) / div;
}
template<class T>
T count(T min, T max, T div, T rem) {
    assert(min >= 0);
    assert(min <= max);
    return count(max + 1, div, rem) - count(min, div, rem);
}

ll mod_mul(ll a, ll b) {
  return (a % mod * b % mod) % mod;
}
ll mod_add(ll a, ll b) {
  return (a % mod + b % mod) % mod;
}
ll mod_sub(ll a, ll b) {
  return (((((a % mod - b % mod) % mod) + mod) % mod) + mod) % mod;
}

int zero, one, two;
int n;
ll dp[500000][3];
ll dfs(int i, int m) {
  if(i == n + 1) {
    if(m == 0) return 1;
    return 0;
  }
  ll &ans = dp[i][m];
  if(ans != -1) return ans;
  // recurrence relation
  ll zans = mod_mul(zero, dfs(i + 1, m));
  ll oans = mod_mul(two, dfs(i + 1, (m + 1) % 3));
  ll tans = mod_mul(one, dfs(i + 1, (m + 2) % 3));
  ans = mod_add(zans, mod_add(oans, tans));
  return ans;
}
bool valid(int n, int a, int b) {
    for(int i = 0; i <= n / a; i++) {
      if((n - a * i) % b == 0) return true;
    }
    return false;
}
bool powerof2(ll n) {
  if(n==0)
   return false;
 
   return (ceil(log2(n)) == floor(log2(n)));
}
bool dfs(ll n, int f) {
  if(n == 0) return 0;
  if(n == 1) return 1;
  if(n & 1) return 1 - dfs(n - 1, 0);
  if(n % 4 != 0) return 1 - dfs(n / 2, 0);
  return 1;

}
void solve() {
    ll n;
    cin >> n;
    if(dfs(n, 0)) {
      cout << "Alice" << nline;
    }
    else cout << "Bob" << nline;
}
  
   

 
int main() {  
  
   ios_base::sync_with_stdio(false);cin.tie(NULL); 
   
   #ifndef ONLINE_JUDGE 
   freopen("input.txt", "r", stdin);  
   freopen("error.txt", "w", stderr); 
   freopen("output.txt", "w", stdout); 
   #endif 
   
  
   int t = 1;
   cin >> t;
   while(t--) { 
     solve() ;
   }

  
  return 0;
}