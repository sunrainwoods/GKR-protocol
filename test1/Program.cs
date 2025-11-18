using System;
using System.Collections.Generic;
using System.IO.Ports;
using System.Linq;
using System.Net.NetworkInformation;
using System.Text;
using System.Threading.Tasks;

namespace test1
{
    internal class Program
    {
        //private static int BinaryToInt(int[] bits)
        //{
        //    int result = 0;
        //    for (int i = 0; i < bits.Length; i++)
        //    {
        //        result |= bits[i] << i;
        //    }
        //    return result;
        //}
        private static int[] IntToBinary(int n, int len)
        {
            int[] bits = new int[len];
            for (int i = 0; i < len; i++)
            {
                bits[i] = (n >> i) & 1;
            }

            //Console.WriteLine("IntToBinary: " + n + " -> " + string.Join(", ", bits));

            return bits;
        }

        private static int Mod(int a, int mod)
        {
            int res = a % mod;
            if (res < 0) res += mod;
            return res;
        }

        private static Func<int[], int[], int[], int> AddPoly(int layer, Node[][] circuit)                  //創建加法多項式
        {
            return (int[] a, int[] b, int[] c) =>
            {
                int s = 0;
                int term = 1;
                for (int i = 0; i < circuit[layer].Length; i++)
                {
                    if (circuit[layer][i].sign == 0)
                    {
                        int[] index = IntToBinary(i, a.Length);
                        for (int j = 0; j < index.Length; j++)
                        {
                            if (index[j] == 1) term *= a[j];
                            else if (index[j] == 0) term *= (1 - a[j]);
                        }
                        index = IntToBinary(circuit[layer][i].left.index, b.Length);
                        for (int j = 0; j < index.Length; j++)
                        {
                            if (index[j] == 1) term *= b[j];
                            else if (index[j] == 0) term *= (1 - b[j]);
                        }
                        index = IntToBinary(circuit[layer][i].right.index, c.Length);
                        for (int j = 0; j < index.Length; j++)
                        {
                            if (index[j] == 1) term *= c[j];
                            else if (index[j] == 0) term *= (1 - c[j]);
                        }
                        s += term;
                    }
                }
                return s;
            };
        }

        private static Func<int[], int[], int[], int> MulPoly(int layer, Node[][] circuit)                      //創建乘法多項式
        {
            return (int[] a, int[] b, int[] c) =>
            {
                int s = 0;
                int term = 1;
                for (int i = 0; i < circuit[layer].Length; i++)
                {
                    if (circuit[layer][i].sign == 1)
                    {
                        int[] index = IntToBinary(i, a.Length);
                        for (int j = 0; j < index.Length; j++)
                        {
                            if (index[j] == 1) term *= a[j];
                            else if (index[j] == 0) term *= (1 - a[j]);
                        }
                        index = IntToBinary(circuit[layer][i].left.index, b.Length);
                        for (int j = 0; j < index.Length; j++)
                        {
                            if (index[j] == 1) term *= b[j];
                            else if (index[j] == 0) term *= (1 - b[j]);
                        }
                        index = IntToBinary(circuit[layer][i].right.index, c.Length);
                        for (int j = 0; j < index.Length; j++)
                        {
                            if (index[j] == 1) term *= c[j];
                            else if (index[j] == 0) term *= (1 - c[j]);
                        }
                        s += term;
                    }
                }
                return s;
            };
        }

        class Node
        {
            public int? value;
            public int sign;                    // 0: + , 1: -
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

            public Node(int value, int index)                  // input node
            {
                this.index = index;
                this.value = value;
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
                if (sign == 0) value = left.value + right.value;
                else if (sign == 1) value = left.value * right.value;
            }
        }



        class Prover
        {
            private Func<int[], int[], int[], int>[] funs;
            private Func<int[], int>[] Vs;
            private int layer;
            private int[] gateNum;
            private int[] bitsLen;
            private int mod;
            private Node[][] circuit;

            public Prover(int layer, int[] gateNum, int[] bitsLen, int mod, Node[][] circuit)
            {
                this.layer = layer;
                this.gateNum = gateNum;
                this.bitsLen = bitsLen;
                this.mod = mod;
                this.circuit = circuit;
                Vs = new Func<int[], int>[layer];
                funs = new Func<int[], int[], int[], int>[layer-1];
                for (int i = 0; i <= layer-1; i++) Vs[i] = make_V(i);
                for (int i = 0; i < layer - 1; i++) funs[i] = make_f(i);
            }

            public int W(int now_lawer, int index)
            {
                return (int)circuit[now_lawer][index].value;
            }

            public Func<int[], int> make_V(int layer)                           //創建層多項式
            {
                return (int[] z) =>
                {
                    int s = 0;
                    for (int i = 0; i < gateNum[layer]; i++)
                    {
                        int term = W(layer, i);
                        int[] indexBits = IntToBinary(i, bitsLen[layer]);
                        for (int j = 0; j < z.Length; j++)
                        {
                            if (indexBits[j] == 1) term *= z[j];
                            else if (indexBits[j] == 0) term *= (1 - z[j]);
                        }
                        s += term;

                        //Console.WriteLine("term: " + term);

                    }

                    Console.WriteLine("s = " + s);

                    return Mod(s, mod);
                };
            }

            public Func<int[], int[], int[], int> make_f(int layer)                                     //創建連接多項式
            {
                return (int[] a, int[] b, int[] c) =>
                {
                    int s = 0;
                    var nextLayerV = Vs[layer + 1];
                    s += AddPoly(layer, circuit)(a, b, c) * (nextLayerV(b) + nextLayerV(c));
                    s += MulPoly(layer, circuit)(a, b, c) * (nextLayerV(b) * nextLayerV(c));
                    return Mod(s, mod);
                };
            }

            public Func<int, int> make_G(int[] fixed_var, int nowLayer)
            {
                return (int z) =>
                {
                    int s = 0;
                    var g = funs[nowLayer];
                    int[] parameter = new int[bitsLen[nowLayer] + bitsLen[nowLayer + 1] + bitsLen[nowLayer + 1]];
                    for (int i = 0; i < fixed_var.Length; i++) parameter[i] = fixed_var[i];
                    parameter[fixed_var.Length] = z;
                    for (int i = 0; i < Math.Pow(2, parameter.Length - fixed_var.Length - 1); i++)
                    {
                        int[] restBits = IntToBinary(i, parameter.Length - fixed_var.Length - 1);
                        for (int j = 0; j < restBits.Length; j++)
                        {
                            parameter[fixed_var.Length + 1 + j] = restBits[j];
                        }
                        s += g(
                            parameter.Take(bitsLen[nowLayer]).ToArray(),
                            parameter.Skip(bitsLen[nowLayer]).Take(bitsLen[nowLayer + 1]).ToArray(),
                            parameter.Skip(bitsLen[nowLayer] + bitsLen[nowLayer + 1]).Take(bitsLen[nowLayer + 1]).ToArray()
                            );

                        //if (nowLayer == 1) Console.WriteLine($"z: {z} ,paramter: " + string.Join(", ", parameter));
                        //if (nowLayer == 1) Console.WriteLine("s: " + s);

                    }
                    return Mod(s, mod);
                };
            }

            public Func<int, int[]> make_l(int layer, int[] fixed_var)
            {
                return (int z) =>
                {
                    int[] b = fixed_var.Skip(bitsLen[layer]).Take(bitsLen[layer + 1]).ToArray();
                    int[] c = fixed_var.Skip(bitsLen[layer] + bitsLen[layer + 1]).Take(bitsLen[layer + 1]).ToArray();
                    int[] l = new int[bitsLen[layer + 1]];
                    for (int i = 0; i < l.Length; i++)
                    {
                        l[i] = Mod(b[i] * (1 - z) + c[i] * z, mod);
                    }
                    return l;
                };
            }

            public Func<int, int> make_q(int layer, int[] fixed_var)                    //創建聲稱多項式
            {
                return (int z) =>
                {
                    int s = 0;
                    var l = make_l(layer, fixed_var);
                    var V_next = Vs[layer + 1];
                    s = V_next(l(z));
                    return Mod(s, mod);
                };
            }

            public Func<int[], int> claimed_D()                                         //結果多項式 (輸出層)
            {
                return (int[] z) =>
                {
                    return Vs[0](z);
                };
            }
        }

        class Verifier
        {
            private Random rand;
            private int mod;

            public Verifier(int mod)
            {
                this.mod = mod;
                rand = new Random();
            }

            public int pickRandom()
            {
                return rand.Next(mod);
            }

            public Func<int[], int> make_input(Node[] input, int bitslen)                           //創建輸入層多項式
            {
                return (int[] z) =>
                {
                    int s = 0;
                    for (int i = 0; i < input.Length; i++)
                    {
                        int term = (int)input[i].value;
                        int[] indexBits = IntToBinary(i, bitslen);
                        for (int j = 0; j < z.Length; j++)
                        {
                            if (indexBits[j] == 1) term *= z[j];
                            else if (indexBits[j] == 0) term *= (1 - z[j]);
                        }
                        s += term;
                    }
                    return Mod(s, mod);
                };
            }
        }

        private static void GKR_Protocol()
        {
            int mod;
            int layer;
            Node[][] circuit;
            int[] gateNum;
            int[] bitsLen;


            while (true)                                             // mod
            {
                Console.Write("mod = ");
                if (!int.TryParse(Console.ReadLine(), out int n))
                {
                    Console.WriteLine("Please enter a valid input.");
                }
                else
                {
                    mod = n;
                    break;
                }
            }


            while (true)                                              // layer
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

            for (int i = 0; i < layer; i++)                                      // gate
            {
                while (true)
                {
                    if (i == 0) Console.Write("(output) ");
                    else if (i == layer - 1) Console.Write("(input) ");
                    Console.Write($"layer {i} = ");
                    string n = Console.ReadLine().Trim();
                    if (i == layer-1)
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
                    else if (n.Distinct().All(c => c == '0' || c == '1') && n.Length > 0)
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

            for (int i = 0; i < layer-1; i++)                                       // connect gates
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
                        if (left < 0 || left >= circuit[i+1].Length ||
                            right < 0 || right >= circuit[i+1].Length)
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

            for (int i = layer - 1; i >= 0; i--)                                    // calculate values
            {
                for (int j = 0; j < circuit[i].Length; j++)
                {
                    circuit[i][j].calculate_value();
                }
            }

            foreach (var n in circuit)                                 // print circuit values
            {
                Console.WriteLine(string.Join(", ", n.Select(x => x.value)));
            }


            //建立P,V
            Prover prover = new Prover(layer, gateNum, bitsLen, mod, circuit);
            Verifier verifier = new Verifier(mod);

            //建立需要的變數
            int[] fixed_var = new int[bitsLen[0]];
            int random_var;
            var claimed_D = prover.claimed_D();
            Func<int, int> claimed_poly;
            int claimed;
            int term;
            Func<int, int[]> l_poly;

            Console.Write("P: send D() and the circuit outputs: ");
            for (int i = 0; i < gateNum[0]; i++) Console.Write(claimed_D(IntToBinary(i, bitsLen[0])) + ", ");
            //Console.WriteLine("\nV: pick fixed_var");
            //for (int i = 0; i < fixed_var.Length; i++) fixed_var[i] = verifier.pickRandom();

            fixed_var[0] = 309;
            fixed_var[1] = 209;

            Console.WriteLine("V: fixed_var = " + string.Join(", ", fixed_var));


            claimed = claimed_D(fixed_var);
            Console.WriteLine("P: claimed D(fixed_var) = " + claimed);

            for (int now_layer = 0; now_layer < layer-1; now_layer++)
            {
                Console.WriteLine("\n sum check ");
                for (int i = 0; i < bitsLen[now_layer + 1] * 2 ; i++)
                {
                    var G = prover.make_G(fixed_var, now_layer);
                    Console.WriteLine($"P: send G{i}");
                    Console.WriteLine($"V: Verifying G{i}(0) + G{i}(1) = claimed");

                    //Console.WriteLine($" G(0): {G(0)}, G(1): {G(1)} ");

                    term = Mod(G(0) + G(1), mod);
                    if (term != claimed) { Console.WriteLine("V: sum check failed"); return; }
                    int s = verifier.pickRandom();
                    Console.WriteLine($"V: pick s{i} = {s}");
                    fixed_var = fixed_var.Append(s).ToArray();
                    claimed = G(s);
                    Console.WriteLine($"P: claimed G{i}(s{i}) = {claimed}");
                    if (now_layer == layer-2 && i == bitsLen[now_layer + 1] * 2 - 1) break;
                    if (i == bitsLen[now_layer + 1] * 2 - 1)
                    {
                        claimed_poly = prover.make_q(now_layer, fixed_var);
                        Console.WriteLine($"P: send claimed_poly q{now_layer + 1}");
                        int[] a = fixed_var.Take(bitsLen[now_layer]).ToArray();
                        int[] b = fixed_var.Skip(bitsLen[now_layer]).Take(bitsLen[now_layer + 1]).ToArray();
                        int[] c = fixed_var.Skip(bitsLen[now_layer] + bitsLen[now_layer + 1]).Take(bitsLen[now_layer + 1]).ToArray();
                        Console.WriteLine("V: sum check final check ");
                        term = Mod((AddPoly(now_layer, circuit)(a, b, c) * (claimed_poly(0) + claimed_poly(1))) + 
                                   (MulPoly(now_layer, circuit)(a, b, c) * (claimed_poly(0) * claimed_poly(1))), mod);

                        //Console.WriteLine("term: " + term);

                        if (claimed != term) { Console.WriteLine("V: final check failed"); return; }
                        Console.WriteLine(" sum check passed ");
                        random_var = verifier.pickRandom();
                        Console.WriteLine($"V: pick r{now_layer + 1} = " + random_var);
                        claimed = claimed_poly(random_var);
                        Console.WriteLine($"P: claimed q{now_layer + 1}(r{now_layer + 1}) = " + claimed);
                        l_poly  = prover.make_l(now_layer, fixed_var);
                        Array.Resize(ref fixed_var, bitsLen[now_layer + 1]);
                        for (int j = 0; j < fixed_var.Length; j++)
                        {
                            fixed_var[j] = l_poly(random_var)[j];

                            //Console.WriteLine(now_layer);
                            //Console.WriteLine($" fixed_var {j}: " + fixed_var[j]);

                        }
                    }
                }
            }
            var input_poly = verifier.make_input(circuit[layer - 1], bitsLen[layer - 1]);
            term = input_poly(fixed_var);
            Console.WriteLine("V: sum check final check ");
            if (claimed != term) { Console.WriteLine("V: final check failed"); return; }
            Console.WriteLine(" sum check passed ");
            Console.WriteLine(" Verifier can trust D() ");
        }

        static void Main(string[] args)
        {
            GKR_Protocol();
        }
    }
}

