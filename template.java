import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.List;
import java.util.StringTokenizer;

public class template {
    static class FastReader {
        BufferedReader br;
        StringTokenizer st;

        public FastReader() {
            br = new BufferedReader(new InputStreamReader(System.in));
        }

        String next() {
            while (st == null || !st.hasMoreElements()) {
                try {
                    st = new StringTokenizer(br.readLine());
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
            return st.nextToken();
        }

        int nextInt() {
            return Integer.parseInt(next());
        }

        long nextLong() {
            return Long.parseLong(next());
        }

        double nextDouble() {
            return Double.parseDouble(next());
        }

        String nextLine() {
            String str = "";
            try {
                if (st != null && st.hasMoreTokens()) {
                    str = st.nextToken("\n");
                } else {
                    str = br.readLine();
                }
            } catch (IOException e) {
                e.printStackTrace();
            }
            return str;
        }
    }

    // CLASSES
    static class Pair implements Comparable<Pair> {
        int vertex1;
        int vertex2;

        public Pair(int vertex1, int vertex2) {
            this.vertex1 = vertex1;
            this.vertex2 = vertex2;
        }

        @Override
        public int compareTo(Pair other) {
            // Primary sort: by vertex1 (ascending)
            if (this.vertex1 != other.vertex1) {
                return Integer.compare(this.vertex1, other.vertex1);
            }
            // Secondary sort: by vertex2 (ascending) if vertex1 is a tie
            return Integer.compare(this.vertex2, other.vertex2);
        }
    }

    public static long gcd(long a, long b) {
        while (b != 0) {
            long temp = b;
            b = a % b;
            a = temp;
        }
        return a;
    }

    public static long lcm(long a, long b) {
        if (a == 0 || b == 0)
            return 0;
        return (a / gcd(a, b)) * b; // Divide first to prevent overflow
    }

    // EXPONENTIATION
    static final int MOD = 1000000007;

    public static long power(long base, long exp) {
        long res = 1;
        base = base % MOD;
        while (exp > 0) {
            // If exp is odd, multiply base with result
            if ((exp & 1) != 0) {
                res = (res * base) % MOD;
            }
            // Square the base and halve the exponent
            base = (base * base) % MOD;
            exp >>= 1;
        }
        return res;
    }

    // FACTORIAL AND nCr
    static long[] fact, invFact;

    public static void precomputeFactorials(int MAXN) {
        fact = new long[MAXN];
        invFact = new long[MAXN];
        fact[0] = 1;
        invFact[0] = 1;

        // Precompute factorials
        for (int i = 1; i < MAXN; i++) {
            fact[i] = (fact[i - 1] * i) % MOD;
        }

        // Precompute inverse factorials
        invFact[MAXN - 1] = power(fact[MAXN - 1], MOD - 2);
        for (int i = MAXN - 2; i >= 1; i--) {
            invFact[i] = (invFact[i + 1] * (i + 1)) % MOD;
        }
    }

    // Calculate nCr % MOD in O(1) time
    public static long nCr(int n, int r) {
        if (r < 0 || r > n)
            return 0;
        long ans = (fact[n] * invFact[r]) % MOD;
        return (ans * invFact[n - r]) % MOD;
    }

    // PRIME SIEVE
    public static void prime_seive(int[] nums) {
        int n = nums.length;
        // first mark all the odd numbers as prime
        for (int i = 3; i < n; i += 2) {
            nums[i] = 1;
        }
        // sieve
        for (int i = 3; i < n; i += 2) {
            // if the curr number is not marked (i.e it is prime)
            if (nums[i] == 1) {
                // the mark all the multiples of this number as non prime
                for (int j = i * i; j < n; j += i) {
                    if (j % i == 0) {
                        nums[j] = 0;
                    }
                }
            }
        }
        // spcl cases
        nums[2] = 1;
        nums[0] = nums[1] = 0;
    }

    // GRAPH
    public static int findParent(int i, int[] parent) {
        if (parent[i] == -1) {
            return i;
        }
        // path compression
        return parent[i] = findParent(parent[i], parent);
    }

    public static void makeUnion(int vertex1, int vertex2, int[] parent, int[] rank) {
        int parent1 = findParent(vertex1, parent);
        int parent2 = findParent(vertex2, parent);

        // make union if there isnt a cycle formation
        if (parent1 != parent2) {
            // make larger chain/tree as the parent
            if (rank[parent1] < rank[parent2]) {
                parent[parent1] = parent2;
                // update the rank
                rank[parent2] += rank[parent1];
            } else {
                parent[parent2] = parent1;
                rank[parent1] += rank[parent2];
            }
        }
    }

    public static boolean containsCycle(int V, List<Pair> edgeList) {
        int[] parent = new int[V];
        int[] rank = new int[V];
        for (int vtx = 0; vtx < V; vtx++) {
            parent[vtx] = -1;
            // initially each element is a disjoint set
            rank[vtx] = 1;
        }

        for (Pair edge : edgeList) {
            int v1 = edge.vertex1;
            int v2 = edge.vertex2;
            int p1 = findParent(v1, parent);
            int p2 = findParent(v2, parent);

            if (p1 == p2)
                return true;
            makeUnion(p1, p2, parent, rank);
        }
        return false;
    }

    // SEGMENT TREES
    static class SegTree {
        long[] tree;
        int n;

        // Initialize with array size
        public SegTree(int n) {
            this.n = n;
            // 4*n is the mathematically safe maximum size for a segment tree array
            tree = new long[4 * n];
        }

        // Call this inside main: build(arr, 1, 0, n - 1)
        public void build(int[] arr, int node, int start, int end) {
            if (start == end) {
                // Leaf node
                tree[node] = arr[start];
                return;
            }
            int mid = start + (end - start) / 2;
            int leftChild = 2 * node;
            int rightChild = 2 * node + 1;

            build(arr, leftChild, start, mid);
            build(arr, rightChild, mid + 1, end);

            // Merge step (Change this for Min/Max/GCD)
            tree[node] = tree[leftChild] + tree[rightChild];
        }

        // Call this to update index 'idx' to 'val': update(1, 0, n - 1, idx, val)
        public void update(int node, int start, int end, int idx, int val) {
            if (start == end) {
                tree[node] = val; // Apply point update
                return;
            }
            int mid = start + (end - start) / 2;
            int leftChild = 2 * node;
            int rightChild = 2 * node + 1;

            if (start <= idx && idx <= mid) {
                update(leftChild, start, mid, idx, val);
            } else {
                update(rightChild, mid + 1, end, idx, val);
            }

            // Merge step (Change this for Min/Max/GCD)
            tree[node] = tree[leftChild] + tree[rightChild];
        }

        // Call this for range [l, r]: query(1, 0, n - 1, l, r)
        public long query(int node, int start, int end, int l, int r) {
            // 1. Range represented by node is completely outside the given range
            if (r < start || end < l) {
                return 0; // Return neutral value (0 for sum, MAX_VALUE for min)
            }
            // 2. Range represented by node is completely inside the given range
            if (l <= start && end <= r) {
                return tree[node];
            }
            // 3. Partial overlap
            int mid = start + (end - start) / 2;
            long leftAns = query(2 * node, start, mid, l, r);
            long rightAns = query(2 * node + 1, mid + 1, end, l, r);

            // Merge step (Change this for Min/Max/GCD)
            return leftAns + rightAns;
        }
    }

    public static void main(String[] args) {
        FastReader in = new FastReader();
        int t = 1;
        t = in.nextInt();
        while (t-- > 0) {
            // CODE HERE

        }
    }
}
