/*
 * author's email: poorna@cs.arizona.edu
 */

// headers   
#include <iostream>
#include <fstream>
#include <queue>
#include <string>
#include <math.h>
#include <stdlib.h>

using namespace std;

// macros
// uncomment these for various levels of debugging
#define TESTSRCH
//#define STRSRCH 1
//#define FASTDBG
//#define DEBUGLEVEL 1
#define ASCIIRANGE 256
#define Assert0(x) if (!(x)) \
{cout << "Error: Assert failed" << endl; }
#define GetI() (SA12[t] < n0 ? SA12[t] * 3 + 1 : (SA12[t] - n0) * 3 + 2)
#define charToLong(x) x-0

// inlines
inline bool leq(long a1, long a2, long b1, long b2) 
{ // lexic. order for pairs
    return(a1 < b1 || a1 == b1 && a2 <= b2);
}                                                   // and triples
inline bool leq(long a1, long a2, long a3, long b1, long b2, long b3) 
{
    return(a1 < b1 || a1 == b1 && leq(a2, a3, b2, b3));
}

// function definitions

// stably sort a[0..n-1] to b[0..n-1] with keys in 0..K from r
void radixPass(long* a, long* b, long* r, long n, long K)
{ // count occurrences
    long* c = new long[K + 1];                          // counter array
    for (long i = 0; i <= K; i++)
    {
        c[i] = 0;         // reset counters
    }

    for (long i = 0; i < n; i++)
    {
        c[r[a[i]]]++;    // count occurences
    }
    for (long i = 0, sum = 0; i <= K; i++) 
    { // exclusive prefix sums
        long t = c[i];  c[i] = sum;  sum += t;
    }
    for (long i = 0; i < n; i++)
    {
        b[c[r[a[i]]]++] = a[i];      // sort
    }
    delete[] c;
}

void printV(char *a, long n, char *comment)
{
    cout << comment << ":";
    for (long i = 0; i < n; i++) 
    {
        cout << a[i] << " ";
    }
    cout << endl;
}
void printV(long* a, long n, char *comment)
{
    cout << comment << ":";
    for (long i = 0; i < n; i++) 
    {
        cout << a[i] << " ";
    }
    cout << endl;
}

bool isPermutation(long *SA, long n) 
{
    bool *seen = new bool[n];
    for (long i = 0; i < n; i++)
    {
        seen[i] = 0;
    }
    for (long i = 0; i < n; i++) 
    { 
        seen[SA[i] - 1] = 1; 
    }

    for (long i = 0; i < n; i++)
    {
        if (!seen[i]) return 0;
    }
    return 1;
}

bool sleq(long *s1, long *s2) {
    if (s1[0] < s2[0])
    {
        return 1;
    }
    if (s1[0] > s2[0]) return 0;
    return sleq(s1 + 1, s2 + 1);
}

// is SA a sorted suffix array for s?
bool isSorted(long *SA, long *s, long n) 
{
    for (long i = 0; i < n - 1; i++)
    {
        if (!sleq(s + SA[i] - 1, s + SA[i + 1] - 1))
        {
            return 0;
        }
    }
    return 1;
}

void longSuffixArray(long* s, long* SA, long n, long K)
{
    long n0 = (n + 2) / 3, n1 = (n + 1) / 3, n2 = n / 3, n02 = n0 + n2;

    long* s12 = new long[n02 + 3];  s12[n02] = s12[n02 + 1] = s12[n02 + 2] = 0;
    long* SA12 = new long[n02 + 3]; SA12[n02] = SA12[n02 + 1] = SA12[n02 + 2] = 0;
    long* s0 = new long[n0];
    long* SA0 = new long[n0];

    // generate positions of mod 1 and mod  2 suffixes
    // the "+(n0-n1)" adds a dummy mod 1 suffix if n%3 == 1
    for (long i = 0, j = 0; i < n + (n0 - n1); i++)
    {
        if (i % 3 != 0)
        {
            s12[j++] = i;
        }
    }

    // lsb radix sort the mod 1 and mod 2 triples
    radixPass(s12, SA12, s + 2, n02, K);
    radixPass(SA12, s12, s + 1, n02, K);
    radixPass(s12, SA12, s, n02, K);

    // find lexicographic names of triples
    int name = 0, c0 = -1, c1 = -1, c2 = -1;
    for (long i = 0; i < n02; i++) 
    {
        if (s[SA12[i]] != c0 || s[SA12[i] + 1] != c1 || s[SA12[i] + 2] != c2)
        {
            name++;  c0 = s[SA12[i]];  c1 = s[SA12[i] + 1];  c2 = s[SA12[i] + 2];
        }
        if (SA12[i] % 3 == 1)
        { 
            s12[SA12[i] / 3] = name; 
        } // left half
        else                 
        { 
            s12[SA12[i] / 3 + n0] = name; 
        } // right half
    }

    // recurse if names are not yet unique
    if (name < n02) 
    {
        longSuffixArray(s12, SA12, n02, name);
        // store unique names in s12 using the suffix array 
        for (long i = 0; i < n02; i++) 
        {
            SA12[i]--;
            s12[SA12[i]] = i + 1;
        }
    }
    else
    {// generate the suffix array of s12 directly
        for (long i = 0; i < n02; i++)
        {
            SA12[s12[i] - 1] = i;
        }
    }

    // stably sort the mod 0 suffixes from SA12 by their first character
    for (long i = 0, j = 0; i < n02; i++)
    {
        if (SA12[i] < n0)
        {
            s0[j++] = 3 * SA12[i];
        }
    }

    radixPass(s0, SA0, s, n0, K);

    // merge sorted SA0 suffixes and sorted SA12 suffixes
    for (long p = 0, t = n0 - n1, k = 0; k < n; k++) 
    {

        long i = GetI(); // pos of current offset 12 suffix
        long j = SA0[p]; // pos of current offset 0  suffix
        if (SA12[t] < n0 ?
            leq(s[i], s12[SA12[t] + n0], s[j], s12[j / 3]) :
            leq(s[i], s[i + 1], s12[SA12[t] - n0 + 1], s[j], s[j + 1], s12[j / 3 + n0]))
        { // suffix from SA12 is smaller
            SA[k] = i + 1;  t++;
            if (t == n02) 
            { // done --- only SA0 suffixes left
                for (k++; p < n0; p++, k++)
                {
                    SA[k] = SA0[p] + 1;
                }
            }
        }
        else 
        {
            SA[k] = j + 1;  p++;
            if (p == n0)  
            { // done --- only SA12 suffixes left
                for (k++; t < n02; t++, k++)
                {
                    SA[k] = GetI() + 1;
                }
            }
        }
    }

    delete[] s12; delete[] SA12; delete[] SA0; delete[] s0;
}

/*
* Wrapper around the real thing. This function is present to serve as an
* interface to the project requirement. The string of chars is converted
* into an array of longs.
*/
void ConstructSuffixArray(char *sChar, long n, long *A)
{
    long *s = new long[n + 3];
    long b = ASCIIRANGE;
    //Yuck!!  
    for (long i = 0; i < n; i++)
    {
        s[i] = charToLong(sChar[i]);
    }

    s[n] = s[n + 1] = s[n + 2] = 0; // put those 0's
    longSuffixArray(s, A, n, b);

    //  Assert0(s[n] == 0);
    //  Assert0(s[n+1] == 0);
    //  Assert0(SA[n] == 0);
    //  Assert0(SA[n+1] == 0);
    Assert0(isPermutation(A, n));
    Assert0(isSorted(A, s, n));

    delete[]s;
}

void ConstructHeightArray(char *S, long N, long *A, long *H)
{
    long n = N;
    long *rank = new long[n];
    for (long i = 0; i < n; i++)
    {
        rank[A[i] - 1] = i;
    }

    long h = 0;
    for (long i = 0; i < n; i++) 
    {
        if (rank[i] < n - 1)
        {
            long k = A[rank[i] + 1] - 1;

            while (S[i + h] == S[k + h]) h++;
            
            H[rank[i]] = h;
            if (h > 0) h--;
        }
    }
}

int lexm(char *s, long m, char *t, long n)
{
    long min = (m < n ? m : n);
    int result = strncmp(s, t, min);
    long answer = -1;
    if (result < 0) 
    { 
        answer = 1; 
        goto done; 
    }
    else if (result > 0) 
    { 
        answer = 0; goto done; 
    }
    else 
    {
        if (m <= n) 
        { 
            answer = 1; goto done; 
        }
        else 
        { 
            answer = 0; goto done; 
        }
    }
done:
#ifdef STRSRCH
    cout << "s: ";
    for (long i = 0; i < m; i++) {
        cout << s[i];
    }
    cout << "|| t : ";
    for (long i = 0; i < n; i++) {
        cout << t[i];
    }
    cout << " " << answer << endl;
#endif
    return answer;
}
#ifdef DELETEME
void testlexm(void)
{
    char s[] = "eleanor";
    char t[] = "rigby";
    if (lexm(s, 7, t, 5, true)) cout << "eleanor rigby" << endl;
    else cout << "father mckenzie" << endl;

    if (lexm(s, 7, s, 7, true)) cout << "picks up the rice in the church" << endl;
    else cout << "died in a grave" << endl;

    if (lexm(t, 5, s, 7, false)) cout << "where do they all come from" << endl;
    else cout << "ahhh.. look at all those lonely people" << endl;

    char p[] = "h";
    char q[] = "hellogoodbye";
    int result = lexm(p, 1, q, 12, true);
    cout << p << " :: " << q << " :: " << result << endl;
    char p1[] = "is", q1[] = "pi";
    result = lexm(q1, 2, p1, 2, false);
    cout << q1 << " :: " << p1 << " :: " << result << endl;

}
#endif
/*
* print matches of the pattern
*/
void printMatches(long N, long *A, long Lo, long Hi)
{
    if (Hi >= N) return;
    cout << endl << "matches are at ";
    for (long i = Lo; i <= Hi; i++) {
        cout << A[i];
    }
    cout << endl;
    return;
}
/*
 * O(mlgn) string search using suffix array A.
 * Using binary search, find leftmost point of the pattern
 * then find the right most point of the pattern.
 * Finally report the low and high indices of the pattern.
 */
void StringSearch(char *S, long N, char *P, int M, long *A,
    long *Lo, long *Hi)
{
    // first find the Lo
    if (lexm(P, (long)M, S + A[0] - 1, N - A[0] + 1)) *Lo = 0;
    else if (!lexm(P, (long)M, S + A[N - 1] - 1, N - A[N - 1] + 1)) *Lo = N;
    else {
        long L = 0, R = N - 1, mid;
        while (R - L > 1)
        {
            mid = (L + R) / 2;
#ifdef DEBUGLEVEL
            cout << "(L,M,R) :: " << L << ", " << mid << ", " << R << endl;
#endif
            if (lexm(P, (long)M, S + A[mid] - 1, N - A[mid] + 1)) R = mid;
            else L = mid;
        }
        *Lo = R;
    }
#ifdef DEBUGLEVEL
    cout << endl << "Search: Lo " << *Lo << endl;
#endif
    //now find the Hi
    //max{k: S[k:n] <m= P or k = -1}
    if (lexm(S + A[N - 1] - 1, N - A[N - 1] + 1, P, (long)M)) {
        *Hi = N - 1;
    }
    else if (0 == strncmp(P, S + A[N - 1] - 1, min((long)M, N - A[N - 1] + 1))) {
        if (M < N - A[N - 1] + 1)
            *Hi = N - 1;
    }
    else if (!lexm(S + A[0] - 1, N - A[0] + 1, P, (long)M)) *Hi = -1;
    else {
        long L = 0, R = N - 1, mid;
        while (R - L>1)
        {
            mid = (L + R) / 2;

#ifdef DEBUGLEVEL
            cout << "(L,M,R) :: " << L << ", " << mid << ", " << R << endl;
#endif
            if (lexm(S + A[mid] - 1, N - A[mid] + 1, P, M)) L = mid;
            else { //
                if (0 == strncmp(P, S + A[mid] - 1, min((long)M, N - A[mid] + 1))) {
                    if (M <= N - A[mid] + 1) { // pattern is fully in suffix
                        L = mid;
                    }
                }
                else {
                    R = mid;
                }
            }
        }
#ifdef DEBUGLEVEL
        cout << " L= " << L << " R= " << R << endl;
#endif
        *Hi = L;
    }
#ifdef DEBUGLEVEL
    cout << " Search: Hi " << *Hi << endl;
#endif
    return;
}

long min(long a, long b)
{
    return (a < b) ? a : b;
}
/*
 * Construct the left- and right-longest-common-prefix arrays L and R,
 * given the height array H for a string of length N.
 * Arrays L and R are already allocated and are indexed from 0
 */

// \forall i \in 1..n
// L[i] = lcp ( S_a[lo], S_a[i] )
// R[i] = lcp ( S_a[i], S_a[hi]) where i = |_(lo + hi)/2 _|
// 0 <= L < Mid < R <= N-1

long reConstructLR(long *H, long N, long *L, long *R,
    long lo, long hi)
{
    long mid = (lo + hi) / 2;
#ifdef DEBUGLEVEL
    cout << "(L,M,R) = " << lo << ", " << mid << ", " << hi << endl;
#endif
    if (hi - lo > 1) {
        L[mid - 1] = reConstructLR(H, N, L, R, lo, mid);
        R[mid - 1] = reConstructLR(H, N, L, R, mid, hi);
        return min(L[mid - 1], R[mid - 1]);
    }
    else {
        return H[lo];
    }
}

void ConstructLandRArrays(long *H, long N, long *L, long *R)
{
    long dummy = reConstructLR(H, N, L, R, 0, N - 1);
}

long lcp(char *a, char *b, long n)
{
    long lcp = 0;
    if (n > 0) {
        while (*a++ == *b++) {
            lcp++; n--;
            if (n == 0) break;
        }
    }
    return lcp;
}


void FasterStringSearch(char *S, long N, char *P, int M, long *A,
    long *L, long *R, long *Lo, long *Hi)
{
    long left, l;
    long right, m, mid, r;

    // find left point
    l = lcp(S + A[0] - 1, P, min(M, N - A[0] + 1));
    r = lcp(S + A[N - 1] - 1, P, min(M, N - A[N - 1] + 1));
#ifdef FASTDBG
    cout << "l= " << l << ", r= " << r << endl;
#endif
    if (l == M)
        *Lo = 0;  // pattern starts at A[0]
    else if ((l < M) && (A[0] + l - 1 < N) && (P[l] < S[A[0] + l - 1]))
        *Lo = 0; // pattern strictly lies to left of A[0]
    else if ((r < M) && (A[N - 1] + r - 1 < N) && (P[r] > S[A[N - 1] + r - 1]))
        *Lo = N; // pattern strictly lies to the right of A[N-1]
    else {
        left = 0; right = N - 1;
        while ((right - left) > 1) {
            mid = (left + right) / 2;
#ifdef FASTDBG
            cout << "l " << l << ", r " << r << " | left " << left << ", mid " << mid << ", right " << right << endl;
#endif
            if (l >= r) {
                if (L[mid - 1] > l) {
                    left = mid;
#ifdef FASTDBG
                    cout << ".";
#endif
                }
                else if (L[mid - 1] == l) {
                    long j = lcp(S + A[mid] + l - 1, P + l, min((M - l), (N - A[mid] - l + 1)));
#ifdef FASTDBG
                    cout << "!" << l << " " << j << " " << M << " " << A[mid] - 1 << "!" << endl;
#endif
                    if (l + j < M && l + j + A[mid] - 1 < N) {
                        if (P[l + j] < S[A[mid] + l + j - 1]) {
                            right = mid; r = l + j; // recurse on left
                        }
                        else {
                            left = mid; l = l + j; //recurse on right
                        }
                    }
                    else {
                        if (l + j + A[mid] - 1 >= N && !(l + j == M)) { // pattern is to the right
                            left = mid; l = l + j;
                        }
                        else if (l + j == M){
                            right = mid; r = l + j;
                        }
                        else { ; }
                    }
                }
                else {
#ifdef FASTDBG
                    cout << "'";
#endif
                    right = mid; r = L[mid - 1];
                }
            }
            else { // l < r 
                if (R[mid - 1] > r) {
#ifdef FASTDBG
                    cout << ".." << endl;
#endif
                    right = mid;
                }
                else if (R[mid - 1] == r) {
                    long j = lcp(S + A[mid] + r - 1, P + r, min((M - r), (N - A[mid] - r + 1)));
#ifdef FASTDBG
                    cout << "!!" << r << " " << j << " " << M << " " << A[mid] - 1 << "!!" << endl;
#endif
                    if (r + j < M && A[mid] + r + j - 1 < N) {
                        if (P[r + j] < S[A[mid] + r + j - 1]) {
                            right = mid; r = r + j; // recurse on left
                        }
                        else {
                            left = mid; l = r + j; //recurse on right
                        }
                    }
                    else {
                        if (r + j == M) {
                            right = mid; r = r + j;
                        }
                        else if (r + j + A[mid] - 1 >= N) {
                            left = mid; l = r + j;
                        }
                        else { ; }
                    }
                }
                else { // R[i] < r
#ifdef FASTDBG
                    cout << "''" << endl;
#endif
                    left = mid; l = R[mid - 1]; // recurse on right
                }
                //if (m==M || P[m] <= S[A[mid]+m]) {
                //  right = mid; r = m;
                //} else {
                //  left = mid; l = m;
                // }
            }

        }
        *Lo = right;
    }
#ifdef FASTDBG
    cout << "Lo: " << *Lo << endl;
#endif

    //now find the right most
    l = lcp(S + A[0] - 1, P, min(M, N - A[0] + 1));
    r = lcp(S + A[N - 1] - 1, P, min(M, N - A[N - 1] + 1));

    if (l < M && A[0] + l - 1 < N && P[l] < S[A[0] + l - 1])
        *Hi = -1; // Pattern is to the left of A[0], => doesn't exist
    else if (r == M)
        *Hi = N - 1;
    else if (r < M && A[N - 1] + r - 1 < N && P[r] >= S[A[N - 1] + r - 1])
        *Hi = N - 1; // Pattern is to the right of A[N-1] => doesn't exist
    else {
        left = 0; right = N - 1;
        while ((right - left) > 1) {
            mid = (left + right) / 2;
#ifdef FASTDBG
            cout << "l " << l << ", r " << r << " | left " << left << ", mid " << mid << ", right " << right << endl;
#endif
            if (l >= r) {
                if (L[mid - 1] > l) {
                    left = mid;
#ifdef FASTDBG
                    cout << ".";
#endif
                }
                else if (L[mid - 1] == l) {
                    long j = lcp(S + A[mid] + l - 1, P + l, min((M - l), (N - A[mid] - l + 1)));
#ifdef FASTDBG
                    cout << "!" << l << " " << j << " " << M << " " << A[mid] - 1 << "!" << endl;
#endif
                    if (l + j < M && l + j + A[mid] - 1 < N) {
                        if (P[l + j] < S[A[mid] + l + j - 1]) {
                            right = mid; r = l + j; // recurse on left
                        }
                        else {
                            left = mid; l = l + j; //recurse on right
                        }
                    }
                    else {
                        if (l + j + A[mid] - 1 >= N && !(l + j == M)) { // pattern is to the right
                            left = mid; l = l + j;
                        }
                        else if (l + j == M){
                            left = mid; l = l + j;
                        }
                        else { ; }
                    }
                }
                else {
#ifdef FASTDBG
                    cout << "'";
#endif
                    right = mid; r = L[mid - 1];
                }
            }
            else { // l < r 
                if (R[mid - 1] > r) {
#ifdef FASTDBG
                    cout << ".." << endl;
#endif
                    right = mid;
                }
                else if (R[mid - 1] == r) {
                    long j = lcp(S + A[mid] + r - 1, P + r, min((M - r), (N - A[mid] - r + 1)));
#ifdef FASTDBG
                    cout << "!!" << r << " " << j << " " << M << " " << A[mid] - 1 << "!!" << endl;
#endif
                    if (r + j < M && A[mid] + r + j - 1 < N) {
                        if (P[r + j] < S[A[mid] + r + j - 1]) {
                            right = mid; r = r + j; // recurse on left
                        }
                        else {
                            left = mid; l = r + j; //recurse on right
                        }
                    }
                    else {
                        if (r + j == M) {
                            left = mid; l = r + j;
                        }
                        else if (r + j + A[mid] - 1 >= N) {
                            left = mid; l = r + j;
                        }
                        else{ ; }
                    }
                }
                else { // R[i] < r
#ifdef FASTDBG
                    cout << "''" << endl;
#endif
                    left = mid; l = R[mid - 1]; // recurse on right
                }
                //if (m==M || P[m] <= S[A[mid]+m]) {
                //  right = mid; r = m;
                //} else {
                //  left = mid; l = m;
                // }
            }
        }

        *Hi = left;
    }
#ifdef FASTDBG
    cout << "Hi " << *Hi << endl;
#endif
}


void printSuffixes(char *s, long n, long *a)
{
    for (long i = 0; i < n; i++)
    {
        cout << "(" << i << "):" << a[i] << ":";
        for (long j = a[i] - 1; j < n; j++)
        {
            cout << s[j];
        }
        cout << endl;
    }
}

void printLandR(long *l, long *r, long n)
{
    cout << endl << "                      :";
    for (long i = 1; i <= n; i++) {
        cout << i << ",";
    }
    cout << endl << "L_p[i]=lcp(A_lo, A_i) :";
    for (long i = 0; i < n; i++) {
        cout << l[i] << ",";
    }
    cout << endl << "R_p[i]=lcp(A_i, A_hi) :";
    for (long i = 0; i < n; i++) {
        cout << r[i] << ",";
    }
    cout << endl;
    return;
}

// test function
void t1(void)
{
    long n = 11;
    char *s = new char[n];
    long *a = new long[n];
    long *h = new long[n];
    long lo = 0, hi = 0;
    strncpy(s, "mississippi", n);
    printV(s, n, "s");
    ConstructSuffixArray(s, n, a);
    printV(a, n, "SA");
    printSuffixes(s, n, a);
    ConstructHeightArray(s, n, a, h);
    printV(h, n - 1, "H");

    long *l = new long[n - 2], *r = new long[n - 2];
    ConstructLandRArrays(h, n, l, r);
    printLandR(l, r, n - 2);

#ifdef STRSRCH
    StringSearch(s, n, "is", 2, a, &lo, &hi);
    cout << lo << "," << hi << endl;
    if (lo <= hi) {
        cout << "Pattern found";
        printMatches(n, a, lo, hi);
    }

    StringSearch(s, n, "si", 2, a, &lo, &hi);
    cout << lo << "," << hi << endl;
    if (lo <= hi) {
        cout << "Pattern found";
        printMatches(n, a, lo, hi);
    }

    StringSearch(s, n, "ss", 2, a, &lo, &hi);
    cout << lo << "," << hi << endl;
    if (lo <= hi) {
        cout << "Pattern found";
        printMatches(n, a, lo, hi);
    }

    StringSearch(s, n, "i", 1, a, &lo, &hi);
    cout << lo << "," << hi << endl;
    if (lo <= hi) {
        cout << "Pattern found";
        printMatches(n, a, lo, hi);
    }
    StringSearch(s, n, "pimp", 4, a, &lo, &hi);
    cout << lo << "," << hi << endl;
    if (lo <= hi) {
        cout << "Pattern found";
        printMatches(n, a, lo, hi);
    }
    else cout << "Pattern not found";

    StringSearch(s, n, "mississippi", 11, a, &lo, &hi);
    cout << lo << "," << hi << endl;
    if (lo <= hi) {
        cout << "Pattern found";
        printMatches(n, a, lo, hi);
    }
    else cout << "Pattern not found";
#endif

#ifdef FASTSTRSRCH
    FasterStringSearch(s, n, "aiss", 4, a, l, r, &lo, &hi);
    cout << lo << "," << hi << endl;
    if (lo <= hi) {
        cout << "Pattern 'aiss' found" << endl;
        printMatches(n, a, lo, hi);
    }
    else cout << "Pattern 'aiss' not found" << endl;

    FasterStringSearch(s, n, "ziss", 4, a, l, r, &lo, &hi);
    cout << lo << "," << hi << endl;
    if (lo <= hi) {
        cout << "Pattern 'ziss' found" << endl;
        printMatches(n, a, lo, hi);
    }
    else cout << "Pattern 'ziss' not found" << endl;

    FasterStringSearch(s, n, "pimz", 4, a, l, r, &lo, &hi);
    cout << lo << "," << hi << endl;
    if (lo <= hi) {
        cout << "Pattern 'pimz' found" << endl;
        printMatches(n, a, lo, hi);
    }
    else cout << "Pattern 'pimz' not found" << endl;

    FasterStringSearch(s, n, "si", 2, a, l, r, &lo, &hi);
    cout << lo << "," << hi << endl;
    if (lo <= hi) {
        cout << "Pattern 'si' found" << endl;
        printMatches(n, a, lo, hi);
    }
    else cout << "Pattern 'si' not found" << endl;

    FasterStringSearch(s, n, "ss", 2, a, l, r, &lo, &hi);
    cout << lo << "," << hi << endl;
    if (lo <= hi) {
        cout << "Pattern 'ss' found" << endl;
        printMatches(n, a, lo, hi);
    }
    else cout << "Pattern 'ss' not found" << endl;

    FasterStringSearch(s, n, "i", 1, a, l, r, &lo, &hi);
    cout << lo << "," << hi << endl;
    if (lo <= hi) {
        cout << "Pattern i found" << endl;
        printMatches(n, a, lo, hi);
    }
    else cout << "Pattern i not found" << endl;

    FasterStringSearch(s, n, "mississippi", 11, a, l, r, &lo, &hi);
    cout << lo << "," << hi << endl;
    if (lo <= hi) {
        cout << "Pattern mississippi found" << endl;
        printMatches(n, a, lo, hi);
    }
    else cout << "Pattern mississippi not found" << endl;

    FasterStringSearch(s, n, "pimp", 4, a, l, r, &lo, &hi);
    cout << lo << "," << hi << endl;
    if (lo <= hi) {
        cout << "Pattern pimp found" << endl;
        printMatches(n, a, lo, hi);
    }
    else cout << "Pattern pimp not found" << endl;
#endif

    delete[]s;
    delete[]a;
}

int verify(char *S, long N, char *P, long M, long *A, long Lo, long Hi)
{
    int answer = -1;
    for (long i = Lo; i <= Hi; i++) {
        if (0 <= i && i < N) {
            if (0 != strncmp(S + A[i] - 1, P, min(M, N - A[i] + 1))) {
                answer = 0;
                cout << "Search error Lo " << Lo << " Hi " << Hi << " at i:" << i << ", A[i]-1:" << A[i] - 1 << endl;
            }
            else answer = 1;
        }
        else {
            answer = 0;
            cout << "Pattern not found. Lo " << Lo << " Hi" << Hi;
        }
    }
    return answer;
}

int main(int argc, char* argv[])
{
    if (argc != 4) {
        cout << "Usage: <execname> stringlength inputfile pattern" << endl;
        return 1;
    }

    long N = atol(argv[1]);
    char* S = new char[N];
    long* A = new long[N];
    long* H = new long[N];
    long* L = new long[N];
    long* R = new long[N];

    fstream file_op(argv[2], ios::in);

    file_op >> S;
#ifdef DEBUGLEVEL
    cout << S << endl;
#endif
    file_op.close();
    ConstructSuffixArray((char*)S, N, A);
    printSuffixes(S, N, A);

    ConstructHeightArray((char*)S, N, A, H);

    char *P = argv[3];
    long M = strlen(P);
    long Lo, Hi;
    int result;
#ifdef TESTSRCH
    StringSearch(S, N, P, M, A, &Lo, &Hi);
    if (1 == (result = verify(S, N, P, M, A, Lo, Hi)))
        cout << "String search worked. Lo" << Lo << ", Hi " << Hi << endl;
    else
        cout << "String search failed code: " << result << " Lo" << Lo << ", Hi " << Hi << endl;
#endif

    ConstructLandRArrays(H, N, L, R);
#ifdef TESTSRCH
    printLandR(L, R, N - 2);

    FasterStringSearch(S, N, P, M, A, L, R, &Lo, &Hi);
    if (1 == (result = verify(S, N, P, M, A, Lo, Hi)))
        cout << "Fast String search worked. Lo" << Lo << ", Hi " << Hi << endl;
    else
        cout << "String search failed code: " << result << " Lo" << Lo << ", Hi " << Hi << endl;
#endif

    delete[] S; delete[] A; delete[] H; delete[] L; delete[] R;
}

#ifdef ASDFASDF
int main(){

    //t1();
    //testlexm();
    return 0;
}
#endif
