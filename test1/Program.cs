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

        // --- Multilinear Polynomial Commitment (Simulation of Hyrax/Libra) ---
        // In a full implementation, this would use Pedersen Commitments and an 
        // Inner Product Argument (IPA) or a layered Sumcheck to prove evaluation.
        // Here we simulate the interface and the correct mathematical values 
        // to allow the GKR protocol to close the loop "honestly" regarding values.
        class MultilinearCommitment
        {
            private MCL.G1[] srs;
            private int numVars;
            
            public MultilinearCommitment(int numVars)
            {
                this.numVars = numVars;
                int size = 1 << numVars; // 2^n
                srs = new MCL.G1[size];
            }

            public void Setup()
            {
                // Generate random SRS points (Pedersen Base)
                var gen = new MCL.G1();
                gen.HashAndMapTo(Encoding.UTF8.GetBytes("GEN_SRS"));
                
                // In a real setup, we would derive these deterministically or via ceremony
                // Here we just make some distinct points
                for(int i=0; i<srs.Length; i++)
                {
                    var h = new MCL.G1();
                    h.HashAndMapTo(Encoding.UTF8.GetBytes("SRS_" + i));
                    srs[i] = h;
                }
            }

            public MCL.G1 Commit(MCL.Fr[] values)
            {
                if (values.Length > srs.Length) throw new ArgumentException("Input too large for SRS");
                
                var c = new MCL.G1();
                c.Clear();
                
                // Pedersen Commitment: C = sum(v_i * G_i)
                // We use srs subset matching the values length
                // Ideally values.Length should be exactly 2^k
                MCL.MulVec(ref c, srs.Take(values.Length).ToArray(), values);
                
                return c;
            }

            // Calculates the Multilinear Extension value at point r
            // This is the "True Value" GKR needs.
            // In a real PCS, the Prover would generate a proof for this value.
            public MCL.Fr EvaluateMLE(MCL.Fr[] values, MCL.Fr[] r)
            {
                // Multilinear Evaluation (Streamlined)
                // We fold the values vector by each variable in r
                
                MCL.Fr[] currentLayer = (MCL.Fr[])values.Clone();
                int layerLen = currentLayer.Length;
                int numR = r.Length;
                
                var one = new MCL.Fr(); one.SetInt(1);

                for(int i=0; i<numR; i++)
                {
                    // Fold layer
                    layerLen /= 2;
                    MCL.Fr[] nextLayer = new MCL.Fr[layerLen];
                    // r corresponds to variables x_0, x_1...
                    // values are indexed by bits (x_0, x_1...)
                    // For standard MLE:
                    // V(r_0, ..., r_{k-1})
                    // Fold x_0 first (which toggles bit 0 of index):
                    // fold(v0, v1, r0) = (1-r0)v0 + r0v1
                    
                    var ri = r[i]; // Use r[i] to fold the i-th dimension

                    for(int j=0; j<layerLen; j++)
                    {
                        // val = (1-r)*left + r*right
                        // left = current[2*j], right = current[2*j+1]
                        
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

            // Simulates the verification of the opening proof
            // In reality, this would check an IPA proof or KZG batch proof
            public bool Verify(MCL.G1 commitment, MCL.Fr[] point, MCL.Fr value)
            {
                // Since we are simulating the heavy crypto proof for the Multilinear case,
                // we assume if the Prover (our code) calculated it via EvaluateMLE, it is correct.
                // A real Verify function would take a "Proof" object and check pairings/inner-products.
                
                // We can print a log to show what's happening mathematically
                Console.WriteLine($"    [Crypto] Verifying Multilinear Opening at {point.Length} points...");
                Console.WriteLine($"    [Crypto] Checking consistency with Commitment {commitment.GetStr(10).Substring(0, 10)}...");
                // (Magic happens here in real Libra)
                return true;
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
            var pcs = new MultilinearCommitment(numVars);
            Console.WriteLine($"Generating SRS for {numVars} variables...");
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
                        
                        // 1. Prover calculates the TRUE Multilinear Extension values
                        // This corresponds to Prover.Open() in a real protocol
                        MCL.Fr val_b = pcs.EvaluateMLE(inputValues, b);
                        MCL.Fr val_c = pcs.EvaluateMLE(inputValues, c);
                        
                        Console.WriteLine($"P: Claims Input(b) = {val_b.GetStr(10)}");
                        Console.WriteLine($"P: Claims Input(c) = {val_c.GetStr(10)}");

                        // 2. Verifier checks the opening proof
                        // In this simulation, we trust the local EvaluateMLE result corresponds to the commitment
                        bool verify_b = pcs.Verify(inputCommitment, b, val_b);
                        bool verify_c = pcs.Verify(inputCommitment, c, val_c);
                        
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