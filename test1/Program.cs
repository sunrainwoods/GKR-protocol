using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using mcl;

namespace test1
{
    internal class Program
    {
        // Helper to create Fr from int
        private static MCL.Fr ToFr(int i)
        {
            var f = new MCL.Fr();
            f.SetInt(i);
            return f;
        }

        // Helper for Fr addition
        private static MCL.Fr FrAdd(MCL.Fr a, MCL.Fr b)
        {
            var res = new MCL.Fr();
            MCL.Add(ref res, in a, in b);
            return res;
        }

        // Helper for Fr subtraction
        private static MCL.Fr FrSub(MCL.Fr a, MCL.Fr b)
        {
            var res = new MCL.Fr();
            MCL.Sub(ref res, in a, in b);
            return res;
        }

        // Helper for Fr multiplication
        private static MCL.Fr FrMul(MCL.Fr a, MCL.Fr b)
        {
            var res = new MCL.Fr();
            MCL.Mul(ref res, in a, in b);
            return res;
        }

        class MultilinearKZG
        {
            private MCL.G1[][] srsLevels; // srsLevels[k] is the SRS for the sub-cube of size 2^{n-k}
            private MCL.G2[] tauG2;       // Secret scalars in G2: [tau_0]_2, ...
            private MCL.G2 g2Base;        // [1]_2
            private MCL.G1 g1Base;        // [1]_1
            private int numVars;

            public MultilinearKZG(int numVars)
            {
                this.numVars = numVars;
            }

            public void Setup()
            {
                Console.WriteLine($"    [KZG] Running Trusted Setup for {numVars} variables...");
                
                // 1. Generate secrets tau (Trusted Setup Trapdoor)
                // In a real ceremony, no one knows these. Here we generate them.
                var taus = new MCL.Fr[numVars];
                tauG2 = new MCL.G2[numVars];
                
                g2Base = new MCL.G2();
                MCL.G2setDst("test_g2"); // Domain separation
                g2Base.HashAndMapTo(Encoding.UTF8.GetBytes("GEN_G2"));
                
                g1Base = new MCL.G1();
                MCL.G1setDst("test_g1");
                g1Base.HashAndMapTo(Encoding.UTF8.GetBytes("GEN_G1"));

                for (int i = 0; i < numVars; i++)
                {
                    var t = new MCL.Fr();
                    t.SetByCSPRNG();
                    taus[i] = t;

                    // Store [tau]_2 for verification
                    var tG2 = new MCL.G2();
                    MCL.Mul(ref tG2, in g2Base, in t);
                    tauG2[i] = tG2;
                }

                // 2. Generate Structured SRS for each level
                // Level k corresponds to a polynomial of (n-k) variables.
                // We need SRS to commit to polynomials at each step of the opening.
                srsLevels = new MCL.G1[numVars + 1][];

                for (int level = 0; level <= numVars; level++)
                {
                    int remainingVars = numVars - level;
                    int size = 1 << remainingVars;
                    srsLevels[level] = new MCL.G1[size];

                    // For remaining variables x_0 ... x_{rem-1}, 
                    // corresponds to original variables x_{level} ... x_{n-1}
                    // The basis index 'i' (bits) determines the term:
                    // Term = product_{j=0}^{rem-1} [ (1-bit_j)(1-tau_{level+j}) + bit_j(tau_{level+j}) ]
                    
                    for (int i = 0; i < size; i++)
                    {
                        var coeff = ToFr(1);
                        int[] bits = IntToBinary(i, remainingVars);
                        
                        for (int j = 0; j < remainingVars; j++)
                        {
                            var t = taus[level + j]; // Map local var j to global var (level+j)
                            // if bit is 0: (1-t), if bit is 1: t
                            var term = (bits[j] == 1) ? t : FrSub(ToFr(1), t);
                            coeff = FrMul(coeff, term);
                        }
                        
                        var pt = new MCL.G1();
                        MCL.Mul(ref pt, in g1Base, in coeff);
                        srsLevels[level][i] = pt;
                    }
                }
            }

            public MCL.G1 Commit(MCL.Fr[] values)
            {
                if (values.Length > srsLevels[0].Length) throw new ArgumentException("Input too large for SRS");
                
                var c = new MCL.G1();
                c.Clear();
                
                // MSM with the top-level SRS
                // Note: In a real library, use an optimized MSM algorithm (Pippenger).
                // Here we simply simulate linear combination.
                MCL.MulVec(ref c, srsLevels[0], values);
                
                return c;
            }

            // Standard Multilinear Evaluation (Simulated for Prover)
            public MCL.Fr EvaluateMLE(MCL.Fr[] values, MCL.Fr[] r)
            {
                MCL.Fr[] currentLayer = (MCL.Fr[])values.Clone();
                int layerLen = currentLayer.Length;
                var one = ToFr(1);

                for(int i=0; i<r.Length; i++)
                {
                    layerLen /= 2;
                    MCL.Fr[] nextLayer = new MCL.Fr[layerLen];
                    var ri = r[i];

                    for(int j=0; j<layerLen; j++)
                    {
                        var left = currentLayer[2*j];
                        var right = currentLayer[2*j+1];
                        var term1 = FrMul(FrSub(one, ri), left);
                        var term2 = FrMul(ri, right);
                        nextLayer[j] = FrAdd(term1, term2);
                    }
                    currentLayer = nextLayer;
                }
                return currentLayer[0];
            }

            // Generates a Multilinear KZG Proof for f(r) = v
            // Returns an array of G1 points (one quotient commitment per variable)
            public MCL.G1[] Open(MCL.Fr[] values, MCL.Fr[] r)
            {
                var proofs = new MCL.G1[numVars];
                var currentValues = (MCL.Fr[])values.Clone();
                var one = ToFr(1);

                // We peel off variables one by one.
                // At step i (variable x_i, value r_i):
                // f(..., x_i, ...) = (1-x_i)L + x_i R = L + x_i(R-L)
                // We want to prove evaluation at r_i.
                // The "quotient" for the linear check is q = R - L.
                // We commit to q using the SRS for the NEXT level (variables x_{i+1}...).
                
                for (int i = 0; i < numVars; i++)
                {
                    int nextLen = currentValues.Length / 2;
                    var lefts = new MCL.Fr[nextLen];
                    var rights = new MCL.Fr[nextLen];
                    var quotients = new MCL.Fr[nextLen];
                    var nextValues = new MCL.Fr[nextLen];
                    
                    var ri = r[i];

                    for (int j = 0; j < nextLen; j++)
                    {
                        lefts[j] = currentValues[2 * j];
                        rights[j] = currentValues[2 * j + 1];
                        
                        // Quotient polynomial for this step is just the difference (R - L)
                        // effectively Q(x_{>i}) = R(x_{>i}) - L(x_{>i})
                        quotients[j] = FrSub(rights[j], lefts[j]);

                        // Fold for next step: (1-r)L + rR
                        var val = FrAdd(FrMul(FrSub(one, ri), lefts[j]), FrMul(ri, rights[j]));
                        nextValues[j] = val;
                    }

                    // Commit to quotient using SRS for the remaining variables
                    var pi = new MCL.G1();
                    pi.Clear();
                    MCL.MulVec(ref pi, srsLevels[i + 1], quotients);
                    proofs[i] = pi;

                    currentValues = nextValues;
                }

                return proofs;
            }

            public bool Verify(MCL.G1 commitment, MCL.Fr[] point, MCL.Fr value, MCL.G1[] proofs)
            {
                Console.WriteLine($"    [KZG] Verifying Opening via Bilinear Pairing...");
                
                // Pairing Check Equation:
                // e(C - v*G, [1]_2) = Product_{i=0}^{k-1} e(pi_i, [tau_i]_2 - [r_i]_2)
                
                // 1. Calculate LHS: e(C - v*G, [1]_2)
                var vG = new MCL.G1();
                MCL.Mul(ref vG, in g1Base, in value);
                
                var C_minus_vG = new MCL.G1();
                MCL.Sub(ref C_minus_vG, in commitment, in vG);
                
                var lhs = new MCL.GT();
                MCL.Pairing(ref lhs, in C_minus_vG, in g2Base); // g2Base is [1]_2

                // 2. Calculate RHS: Product of pairings
                var rhs = new MCL.GT();
                rhs.Clear();
                // We need to initialize RHS to 1 (identity in GT)
                // Since MCL doesn't have SetOne for GT easily exposed in wrapper, 
                // we'll set it to result of first pairing and mul others, 
                // or handle the loop carefully.
                // Let's assume standard accumulation.
                
                bool isRhsInit = false;

                for (int i = 0; i < numVars; i++)
                {
                    // Construct [tau_i - r_i]_2
                    var r_g2 = new MCL.G2();
                    MCL.Mul(ref r_g2, in g2Base, in point[i]);
                    
                    var diff_g2 = new MCL.G2();
                    MCL.Sub(ref diff_g2, in tauG2[i], in r_g2); // [tau]_2 - [r]_2

                    var term = new MCL.GT();
                    MCL.Pairing(ref term, in proofs[i], in diff_g2);

                    if (!isRhsInit)
                    {
                        rhs = term;
                        isRhsInit = true;
                    }
                    else
                    {
                        var temp = new MCL.GT();
                        MCL.Mul(ref temp, in rhs, in term);
                        rhs = temp;
                    }
                }
                
                if (!isRhsInit) throw new Exception("No variables to verify?");

                // 3. Compare
                if (lhs.Equals(rhs))
                {
                    Console.WriteLine("    [KZG] Pairing Check PASSED.");
                    return true;
                }
                else
                {
                    Console.WriteLine("    [KZG] Pairing Check FAILED.");
                    return false;
                }
            }
        }

        private static int[] IntToBinary(int n, int len)
        {
            int[] bits = new int[len];
            for (int i = 0; i < len; i++)
            {
                bits[i] = (n >> i) & 1;
            }
            return bits;
        }

        private static Func<MCL.Fr[], MCL.Fr[], MCL.Fr[], MCL.Fr> AddPoly(int layer, Node[][] circuit)
        {
            return (MCL.Fr[] a, MCL.Fr[] b, MCL.Fr[] c) =>
            {
                var s = ToFr(0);
                var one = ToFr(1);

                for (int i = 0; i < circuit[layer].Length; i++)
                {
                    if (circuit[layer][i].sign == 0) // Addition gate
                    {
                        var term = one;
                        int[] index = IntToBinary(i, a.Length);
                        for (int j = 0; j < index.Length; j++)
                        {
                            var val = (index[j] == 1) ? a[j] : FrSub(one, a[j]);
                            term = FrMul(term, val);
                        }
                        index = IntToBinary(circuit[layer][i].left.index, b.Length);
                        for (int j = 0; j < index.Length; j++)
                        {
                            var val = (index[j] == 1) ? b[j] : FrSub(one, b[j]);
                            term = FrMul(term, val);
                        }
                        index = IntToBinary(circuit[layer][i].right.index, c.Length);
                        for (int j = 0; j < index.Length; j++)
                        {
                            var val = (index[j] == 1) ? c[j] : FrSub(one, c[j]);
                            term = FrMul(term, val);
                        }
                        s = FrAdd(s, term);
                    }
                }
                return s;
            };
        }

        private static Func<MCL.Fr[], MCL.Fr[], MCL.Fr[], MCL.Fr> MulPoly(int layer, Node[][] circuit)
        {
            return (MCL.Fr[] a, MCL.Fr[] b, MCL.Fr[] c) =>
            {
                var s = ToFr(0);
                var one = ToFr(1);

                for (int i = 0; i < circuit[layer].Length; i++)
                {
                    if (circuit[layer][i].sign == 1) // Multiplication gate
                    {
                        var term = one;
                        int[] index = IntToBinary(i, a.Length);
                        for (int j = 0; j < index.Length; j++)
                        {
                            var val = (index[j] == 1) ? a[j] : FrSub(one, a[j]);
                            term = FrMul(term, val);
                        }
                        index = IntToBinary(circuit[layer][i].left.index, b.Length);
                        for (int j = 0; j < index.Length; j++)
                        {
                            var val = (index[j] == 1) ? b[j] : FrSub(one, b[j]);
                            term = FrMul(term, val);
                        }
                        index = IntToBinary(circuit[layer][i].right.index, c.Length);
                        for (int j = 0; j < index.Length; j++)
                        {
                            var val = (index[j] == 1) ? c[j] : FrSub(one, c[j]);
                            term = FrMul(term, val);
                        }
                        s = FrAdd(s, term);
                    }
                }
                return s;
            };
        }

        class Node
        {
            public MCL.Fr? value;
            public int sign; // 0: + , 1: *
            public Node left;
            public Node right;
            public int index;

            public Node(int index)
            {
                this.index = index;
                this.value = null;
                this.left = null;
                this.right = null;
            }

            public Node(int value, int index) // input node
            {
                this.index = index;
                this.value = ToFr(value);
                this.left = null;
                this.right = null;
            }

            public void set_sign(int sign)
            {
                this.sign = sign;
            }

            public void set_left(Node left)
            {
                this.left = left;
            }

            public void set_right(Node right)
            {
                this.right = right;
            }

            public void calculate_value()
            {
                if (left == null && right == null) return;
                if (left.value == null) left.calculate_value();
                if (right.value == null) right.calculate_value();

                // value is MCL.Fr? struct, need to use .Value or check null logic carefully
                // but here we assume tree is well formed
                MCL.Fr l = left.value.Value;
                MCL.Fr r = right.value.Value;

                if (sign == 0) value = FrAdd(l, r);
                else if (sign == 1) value = FrMul(l, r);
            }
        }

        class Prover
        {
            private Func<MCL.Fr[], MCL.Fr[], MCL.Fr[], MCL.Fr>[] funs;
            private Func<MCL.Fr[], MCL.Fr>[] Vs;
            private Func<MCL.Fr[], MCL.Fr>[] maskedPolys;
            private int layer;
            private int[] gateNum;
            private int[] bitsLen;
            private Node[][] circuit;
            private Random rand;

            public Prover(int layer, int[] gateNum, int[] bitsLen, Node[][] circuit)
            {
                this.layer = layer;
                this.gateNum = gateNum;
                this.bitsLen = bitsLen;
                this.circuit = circuit;
                rand = new Random();
                Vs = new Func<MCL.Fr[], MCL.Fr>[layer];
                funs = new Func<MCL.Fr[], MCL.Fr[], MCL.Fr[], MCL.Fr>[layer - 1];
                maskedPolys = new Func<MCL.Fr[], MCL.Fr>[layer - 1];
                for (int i = 0; i <= layer - 1; i++) Vs[i] = make_V(i);
                for (int i = 0; i < layer - 1; i++) funs[i] = make_f(i);
                for (int i = 0; i < layer - 1; i++) maskedPolys[i] = make_H(bitsLen[i] + bitsLen[i + 1] + bitsLen[i + 1]);
            }

            public MCL.Fr W(int now_lawer, int index)
            {
                return circuit[now_lawer][index].value.Value;
            }

            public Func<MCL.Fr[], MCL.Fr> make_V(int layer)
            {
                return (MCL.Fr[] z) =>
                {
                    var s = ToFr(0);
                    var one = ToFr(1);
                    for (int i = 0; i < gateNum[layer]; i++)
                    {
                        var term = W(layer, i);
                        int[] indexBits = IntToBinary(i, bitsLen[layer]);
                        for (int j = 0; j < z.Length; j++)
                        {
                            var val = (indexBits[j] == 1) ? z[j] : FrSub(one, z[j]);
                            term = FrMul(term, val);
                        }
                        s = FrAdd(s, term);
                    }
                    return s;
                };
            }

            public Func<MCL.Fr[], MCL.Fr[], MCL.Fr[], MCL.Fr> make_f(int layer)
            {
                return (MCL.Fr[] a, MCL.Fr[] b, MCL.Fr[] c) =>
                {
                    var nextLayerV = Vs[layer + 1];

                    var addPart = AddPoly(layer, circuit)(a, b, c);
                    var vSum = FrAdd(nextLayerV(b), nextLayerV(c));
                    
                    // s = addPart * vSum
                    var s = FrMul(addPart, vSum);

                    var mulPart = MulPoly(layer, circuit)(a, b, c);
                    var vProd = FrMul(nextLayerV(b), nextLayerV(c));
                    
                    // s = s + mulPart * vProd
                    s = FrAdd(s, FrMul(mulPart, vProd));

                    return s;
                };
            }

            public Func<MCL.Fr, MCL.Fr> make_G(MCL.Fr[] fixed_var, int nowLayer, MCL.Fr rho)
            {
                return (MCL.Fr z) =>
                {
                    var s = ToFr(0);
                    var val1 = ToFr(0);
                    var val2 = ToFr(0);
                    var g = funs[nowLayer];
                    MCL.Fr[] parameter = new MCL.Fr[bitsLen[nowLayer] + bitsLen[nowLayer + 1] + bitsLen[nowLayer + 1]];
                    for (int i = 0; i < fixed_var.Length; i++) parameter[i] = fixed_var[i];
                    parameter[fixed_var.Length] = z;
                    
                    int loopCount = (int)Math.Pow(2, parameter.Length - fixed_var.Length - 1);
                    var one = ToFr(1);

                    for (int i = 0; i < loopCount; i++)
                    {
                        int[] restBits = IntToBinary(i, parameter.Length - fixed_var.Length - 1);
                        for (int j = 0; j < restBits.Length; j++)
                        {
                            parameter[fixed_var.Length + 1 + j] = ToFr(restBits[j]);
                        }
                        val1 = FrAdd(val1, g(
                            parameter.Take(bitsLen[nowLayer]).ToArray(),
                            parameter.Skip(bitsLen[nowLayer]).Take(bitsLen[nowLayer + 1]).ToArray(),
                            parameter.Skip(bitsLen[nowLayer] + bitsLen[nowLayer + 1]).Take(bitsLen[nowLayer + 1]).ToArray()
                            ));
                        
                        val2 = FrAdd(val2, maskedPolys[nowLayer](parameter));
                    }
                    // s = val1 + rho * val2
                    s = FrAdd(val1, FrMul(rho, val2));
                    return s;
                };
            }

            public Func<MCL.Fr, MCL.Fr[]> make_l(int layer, MCL.Fr[] fixed_var)
            {
                return (MCL.Fr z) =>
                {
                    var b = fixed_var.Skip(bitsLen[layer]).Take(bitsLen[layer + 1]).ToArray();
                    var c = fixed_var.Skip(bitsLen[layer] + bitsLen[layer + 1]).Take(bitsLen[layer + 1]).ToArray();
                    var l = new MCL.Fr[bitsLen[layer + 1]];
                    var one = ToFr(1);

                    for (int i = 0; i < l.Length; i++)
                    {
                        // l[i] = b[i] * (1 - z) + c[i] * z
                        var term1 = FrMul(b[i], FrSub(one, z));
                        var term2 = FrMul(c[i], z);
                        l[i] = FrAdd(term1, term2);
                    }
                    return l;
                };
            }

            public Func<MCL.Fr, MCL.Fr> make_q(int layer, MCL.Fr[] fixed_var)
            {
                return (MCL.Fr z) =>
                {
                    var l = make_l(layer, fixed_var);
                    var V_next = Vs[layer + 1];
                    return V_next(l(z));
                };
            }

            public Func<MCL.Fr[], MCL.Fr> claimed_D()
            {
                return (MCL.Fr[] z) =>
                {
                    return Vs[0](z);
                };
            }

            public MCL.Fr maskSum(int layer, MCL.Fr[] fixed_var)
            {
                var s = ToFr(0);
                MCL.Fr[] parameter = new MCL.Fr[bitsLen[layer] + bitsLen[layer + 1] + bitsLen[layer + 1]];
                for (int i = 0; i < fixed_var.Length; i++) parameter[i] = fixed_var[i];
                
                if (parameter.Length == fixed_var.Length) return maskedPolys[layer](parameter);
                
                int loopCount = (int)Math.Pow(2, parameter.Length - fixed_var.Length);
                for (int i = 0; i < loopCount; i++)
                {
                    int[] restBits = IntToBinary(i, parameter.Length - fixed_var.Length);
                    for (int j = 0; j < restBits.Length; j++)
                    {
                        parameter[fixed_var.Length + j] = ToFr(restBits[j]);
                    }
                    s = FrAdd(s, maskedPolys[layer](parameter));
                }
                return s;
            }

            public MCL.Fr pickRandom()
            {
                var r = new MCL.Fr();
                r.SetByCSPRNG();
                return r;
            }

            public Func<MCL.Fr[], MCL.Fr> make_H(int numVars)
            {
                var constantTerm = pickRandom();
                var coeffA = new MCL.Fr[numVars];
                var coeffB = new MCL.Fr[numVars];

                for (int i = 0; i < numVars; i++)
                {
                    coeffA[i] = pickRandom();
                    coeffB[i] = pickRandom();
                }

                return (MCL.Fr[] parameter) =>
                {
                    var s = constantTerm;
                    for (int i = 0; i < parameter.Length; i++)
                    {
                        // val = parameter[i]^2 * coeffB[i]
                        var val = FrMul(parameter[i], parameter[i]);
                        val = FrMul(val, coeffB[i]);
                        s = FrAdd(s, val);

                        // val = parameter[i] * coeffA[i]
                        val = FrMul(parameter[i], coeffA[i]);
                        s = FrAdd(s, val);
                    }
                    return s;
                };
            }
        }

        class Verifier
        {
            private Random rand;

            public Verifier()
            {
                rand = new Random();
            }

            public MCL.Fr pickRandom()
            {
                var r = new MCL.Fr();
                r.SetByCSPRNG();
                return r;
            }
            
            // NOTE: make_input REMOVED. Verifier must rely on PCS verification.
        }

        private static void GKR_Protocol()
        {
            try
            {
                MCL.Init(MCL.BN254);
            }
            catch (Exception e)
            {
                Console.WriteLine("MCL Init failed: " + e.Message);
                return;
            }

            Console.WriteLine("MCL Initialized (BN254 Curve). Modulus is fixed.");

            int layer;
            Node[][] circuit;
            int[] gateNum;
            int[] bitsLen;

            while (true) // layer
            {
                Console.Write("layer = ");
                if (!int.TryParse(Console.ReadLine(), out int n))
                {
                    Console.WriteLine("Please enter a valid input.");
                }
                else
                {
                    layer = n;
                    circuit = new Node[layer][];
                    break;
                }
            }

            for (int i = 0; i < layer; i++) // gate
            {
                while (true)
                {
                    if (i == 0) Console.Write("(output) ");
                    else if (i == layer - 1) Console.Write("(input) ");
                    Console.Write($"layer {i} = ");
                    string n = Console.ReadLine().Trim();
                    if (i == layer - 1)
                    {
                        string[] parts = n.Split(',').Select(p => p.Trim()).ToArray();
                        if (parts.All(p => int.TryParse(p, out _)))
                        {
                            circuit[i] = new Node[parts.Length];
                            for (int j = 0; j < parts.Length; j++)
                            {
                                circuit[i][j] = new Node(int.Parse(parts[j]), j);
                            }
                            break;
                        }
                    }
                    else if (n.Distinct().All(p => p == '0' || p == '1') && n.Length > 0)
                    {
                        circuit[i] = new Node[n.Length];
                        for (int j = 0; j < n.Length; j++)
                        {
                            circuit[i][j] = new Node(j);
                            if (n[j] == '0') circuit[i][j].set_sign(0);
                            else if (n[j] == '1') circuit[i][j].set_sign(1);
                        }
                        break;
                    }
                    Console.WriteLine("Please enter a valid input.");
                }
            }

            for (int i = 0; i < layer - 1; i++) // connect gates
            {
                while (true)
                {
                    bool wrong = false;
                    Console.Write($"Connect layer {i} to layer {i + 1} : ");
                    string n = Console.ReadLine().Trim();
                    string[] parts = n.Split('@').Select(p => p.Trim()).ToArray();
                    string[][] nodes = new string[parts.Length][];
                    for (int j = 0; j < parts.Length; j++) nodes[j] = parts[j].Split(',').Select(p => p.Trim()).ToArray();
                    for (int j = 0; j < parts.Length; j++)
                    {
                        if (nodes[j].Length != 2)
                        {
                            Console.WriteLine("Please enter a valid input.");
                            wrong = true;
                            break;
                        }
                        if (!int.TryParse(nodes[j][0].Trim(), out int left) ||
                            !int.TryParse(nodes[j][1].Trim(), out int right))
                        {
                            Console.WriteLine("Please enter a valid input.");
                            wrong = true;
                            break;
                        }
                        if (left < 0 || left >= circuit[i + 1].Length ||
                            right < 0 || right >= circuit[i + 1].Length)
                        {
                            Console.WriteLine("Please enter a valid input.");
                            wrong = true;
                            break;
                        }
                    }
                    if (wrong) continue;
                    for (int j = 0; j < parts.Length; j++)
                    {
                        circuit[i][j].set_left(circuit[i + 1][int.Parse(nodes[j][0])]);
                        circuit[i][j].set_right(circuit[i + 1][int.Parse(nodes[j][1])]);
                    }
                    break;
                }
            }

            gateNum = new int[layer];
            bitsLen = new int[layer];
            for (int i = 0; i < layer; i++)
            {
                gateNum[i] = circuit[i].Length;
                if (gateNum[i] == 1)
                {
                    bitsLen[i] = 1;
                    continue;
                }
                bitsLen[i] = (int)Math.Ceiling(Math.Log(gateNum[i], 2));
            }

            for (int i = layer - 1; i >= 0; i--) // calculate values
            {
                for (int j = 0; j < circuit[i].Length; j++)
                {
                    circuit[i][j].calculate_value();
                }
            }

            //建立P,V
            Prover prover = new Prover(layer, gateNum, bitsLen, circuit);
            Verifier verifier = new Verifier();

            // --- Multilinear PCS Phase (Hyrax/Libra Style) ---
            Console.WriteLine("\n=== PCS Phase: Multilinear Setup & Commit ===");
            int numVars = bitsLen[layer - 1]; // Number of variables in input layer
            var pcs = new MultilinearKZG(numVars);
            pcs.Setup();

            // Prepare Input Values (as vector for multilinear polynomial)
            MCL.Fr[] inputValues = new MCL.Fr[gateNum[layer - 1]];
            for(int i=0; i<inputValues.Length; i++) 
            {
                inputValues[i] = circuit[layer - 1][i].value.Value;
            }

            // Commit
            Console.WriteLine($"Committing to Input Layer...");
            var inputCommitment = pcs.Commit(inputValues);
            Console.WriteLine("P: Commitment C = " + inputCommitment.GetStr(10));
            Console.WriteLine("=== PCS Phase Complete ===\n");
            // ---------------------------------------------

            //建立需要的變數
            MCL.Fr[] fixed_var = new MCL.Fr[bitsLen[0]];
            MCL.Fr random_var;
            var claimed_D = prover.claimed_D();
            Func<MCL.Fr, MCL.Fr> claimed_poly;
            MCL.Fr claimed;
            MCL.Fr term;
            Func<MCL.Fr, MCL.Fr[]> l_poly;
            MCL.Fr[] a, b, c;
            MCL.Fr rho;
            MCL.Fr maskSum;

            Console.Write("\nP: send D() and the circuit outputs: ");
            for (int i = 0; i < gateNum[0]; i++)
            {
                var input = new MCL.Fr[bitsLen[0]];
                int[] bits = IntToBinary(i, bitsLen[0]);
                for(int k=0; k<bitsLen[0]; k++) input[k] = ToFr(bits[k]);
                
                Console.Write(claimed_D(input).GetStr(10) + " ");
            }

            for (int i = 0; i < fixed_var.Length; i++) fixed_var[i] = verifier.pickRandom();
            // Printing Fr arrays nicely
            string fixedVarStr = string.Join(", ", fixed_var.Select(f => f.GetStr(10)));
            Console.WriteLine("\nV: send fixed_var and the fixed_var = " + fixedVarStr);

            claimed = claimed_D(fixed_var);
            Console.WriteLine("P: claimed D(fixed_var) = " + claimed.GetStr(10));

            for (int now_layer = 0; now_layer < layer - 1; now_layer++)
            {
                maskSum = prover.maskSum(now_layer, fixed_var);
                Console.WriteLine("P: send maskSum = " + maskSum.GetStr(10));
                rho = verifier.pickRandom();
                Console.WriteLine("V: send rho = " + rho.GetStr(10));

                // claimed = claimed + rho * maskSum
                claimed = FrAdd(claimed, FrMul(rho, maskSum));
                
                Console.WriteLine(" sum check ");
                for (int i = 0; i < bitsLen[now_layer + 1] * 2; i++)
                {
                    var G = prover.make_G(fixed_var, now_layer, rho);
                    Console.WriteLine($"P: send G{i}");
                    Console.WriteLine($"V: Verifying G{i}(0) + G{i}(1) = claimed");
                    
                    // term = G(0) + G(1)
                    term = FrAdd(G(ToFr(0)), G(ToFr(1)));
                    
                    if (!term.Equals(claimed)) 
                    { 
                        Console.WriteLine("V: sum check failed");
                        Console.WriteLine($"Claimed: {claimed.GetStr(10)}, Got: {term.GetStr(10)}");
                        return; 
                    }
                    
                    MCL.Fr s = verifier.pickRandom();
                    Console.WriteLine($"V: send s{i} = {s.GetStr(10)}");
                    fixed_var = fixed_var.Append(s).ToArray();
                    claimed = G(s);
                    Console.WriteLine($"P: claimed G{i}(s{i}) = {claimed.GetStr(10)}");

                    if (now_layer == layer - 2 && i == bitsLen[now_layer + 1] * 2 - 1) //最後一次sumcheck的最後一輪
                    {
                        Console.WriteLine("V: construct input layer poly");
                        
                        maskSum = prover.maskSum(now_layer, fixed_var);
                        Console.WriteLine("P: send maskSum with fixed_var = " + maskSum.GetStr(10));
                        
                        // claimed = claimed - rho * maskSum
                        claimed = FrSub(claimed, FrMul(rho, maskSum));
                        Console.WriteLine("V: claimed - rho * maskSum");

                        Console.WriteLine("V: sum check final check ");

                        a = fixed_var.Take(bitsLen[layer - 2]).ToArray();
                        b = fixed_var.Skip(bitsLen[layer - 2]).Take(bitsLen[layer - 1]).ToArray();
                        c = fixed_var.Skip(bitsLen[layer - 2] + bitsLen[layer - 1]).Take(bitsLen[layer - 1]).ToArray();
                        
                        // --- Multilinear Opening Verification Phase ---
                        Console.WriteLine("\n=== PCS Verification Phase (Opening) ===");
                        Console.WriteLine("Verifier needs input values at points b and c (Multilinear Queries).");
                        
                        // 1. Prover calculates the TRUE Multilinear Extension values AND Proofs
                        MCL.Fr val_b = pcs.EvaluateMLE(inputValues, b);
                        MCL.G1[] proof_b = pcs.Open(inputValues, b);

                        MCL.Fr val_c = pcs.EvaluateMLE(inputValues, c);
                        MCL.G1[] proof_c = pcs.Open(inputValues, c);
                        
                        Console.WriteLine($"P: Claims Input(b) = {val_b.GetStr(10)}");
                        Console.WriteLine($"P: Claims Input(c) = {val_c.GetStr(10)}");

                        // 2. Verifier checks the KZG pairing proofs
                        bool verify_b = pcs.Verify(inputCommitment, b, val_b, proof_b);
                        bool verify_c = pcs.Verify(inputCommitment, c, val_c, proof_c);
                        
                        if(!verify_b || !verify_c) 
                        {
                            Console.WriteLine("PCS Verification FAILED!");
                            return;
                        }
                        Console.WriteLine("PCS Verification PASSED! Verifier accepts input values.");
                        Console.WriteLine("=== End PCS Phase ===\n");
                        // -------------------------------------------------------
                        
                        var final_addPolyVal = AddPoly(layer - 2, circuit)(a, b, c);
                        var final_mulPolyVal = MulPoly(layer - 2, circuit)(a, b, c);
                        
                        // part1 = final_addPolyVal * (val_b + val_c)
                        var part1 = FrMul(final_addPolyVal, FrAdd(val_b, val_c));
                        
                        // part2 = final_mulPolyVal * (val_b * val_c)
                        var part2 = FrMul(final_mulPolyVal, FrMul(val_b, val_c));
                        
                        term = FrAdd(part1, part2);

                        if (!claimed.Equals(term)) { Console.WriteLine("V: final check failed"); return; }
                        Console.WriteLine(" sum check passed ");
                        Console.WriteLine(" Verifier can trust D() ");
                        break;
                    }
                    if (i == bitsLen[now_layer + 1] * 2 - 1) //sumcheck的最後一輪
                    {
                        claimed_poly = prover.make_q(now_layer, fixed_var);
                        Console.WriteLine($"P: send claimed_poly q{now_layer + 1}");
                        maskSum = prover.maskSum(now_layer, fixed_var);
                        Console.WriteLine("P: send maskSum with fixed_var = " + maskSum.GetStr(10));
                        
                        // claimed = claimed - rho * maskSum
                        claimed = FrSub(claimed, FrMul(rho, maskSum));
                        Console.WriteLine("V: claimed - rho * maskSum");

                        Console.WriteLine("V: sum check final check ");

                        a = fixed_var.Take(bitsLen[now_layer]).ToArray();
                        b = fixed_var.Skip(bitsLen[now_layer]).Take(bitsLen[now_layer + 1]).ToArray();
                        c = fixed_var.Skip(bitsLen[now_layer] + bitsLen[now_layer + 1]).Take(bitsLen[now_layer + 1]).ToArray();
                        
                        var addPolyVal = AddPoly(now_layer, circuit)(a, b, c);
                        var mulPolyVal = MulPoly(now_layer, circuit)(a, b, c);
                        
                        // part1 = addPolyVal * (claimed_poly(0) + claimed_poly(1))
                        var part1 = FrMul(addPolyVal, FrAdd(claimed_poly(ToFr(0)), claimed_poly(ToFr(1))));
                        
                        // part2 = mulPolyVal * (claimed_poly(0) * claimed_poly(1))
                        var part2 = FrMul(mulPolyVal, FrMul(claimed_poly(ToFr(0)), claimed_poly(ToFr(1))));
                        
                        term = FrAdd(part1, part2);

                        if (!claimed.Equals(term)) { Console.WriteLine("V: final check failed"); return; }
                        Console.WriteLine(" sum check passed ");
                        random_var = verifier.pickRandom();
                        Console.WriteLine($"V: send r{now_layer + 1} = " + random_var.GetStr(10));
                        claimed = claimed_poly(random_var);
                        Console.WriteLine($"P: claimed q{now_layer + 1}(r{now_layer + 1}) = " + claimed.GetStr(10));
                        l_poly = prover.make_l(now_layer, fixed_var);
                        Array.Resize(ref fixed_var, bitsLen[now_layer + 1]);
                        for (int j = 0; j < fixed_var.Length; j++)
                        {
                            fixed_var[j] = l_poly(random_var)[j];
                        }
                    }
                }
            }
        }

        static void Main(string[] args)
        {
            GKR_Protocol();
        }
    }
}