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
            return bits.Reverse().ToArray();
        }

        private static int Mod(int a, int mod)
        {
            int res = a % mod;
            if (res < 0) res += mod;
            return res;
        }

        //private static long Add(int layer, int[] x, int[] y, int[] z)
        //{
        //    int a = BinaryToInt(x);
        //    int b = BinaryToInt(y);
        //    int c = BinaryToInt(z);
        //    if (layer == 2)
        //    {
        //        if (a == 0 && b == 0 && c == 1) return 1;
        //        if (a == 3 && b == 6 && c == 7) return 1;
        //    }
        //    else if (layer == 1)
        //    {
        //        if (a == 1 && b == 2 && c == 3) return 1;
        //    }
        //    else if (layer == 0)
        //    {
        //        if (a == 0 && b == 0 && c == 1) return 1;
        //    }
        //    return 0;
        //}
        private static Func<int[], int[], int[], int> AddPoly(int layer)
        {
            return (int[] a, int[] b, int[] c) =>
            {
                int s = 0;
                if (layer == 2)
                {
                    s += (1 - a[0]) * (1 - a[1]) * (1 - b[0]) * (1 - b[1]) * (1 - b[2]) * (1 - c[0]) * (1 - c[1]) * c[2];
                    s += a[0] * a[1] * b[0] * b[1] * (1 - b[2]) * c[0] * c[1] * c[2];
                }
                else if (layer == 1)
                {
                    s += a[0] * b[0] * (1 - b[1]) * c[0] * c[1];
                }
                else if (layer == 0)
                {
                    s += (1 - a[0]) * (1 - b[0]) * c[0];
                }
                return s;
            };
        }
        //private static long Mul(int layer, int[] x, int[] y, int[] z)
        //{
        //    int a = BinaryToInt(x);
        //    int b = BinaryToInt(y);
        //    int c = BinaryToInt(z);
        //    if (layer == 2)
        //    {
        //        if (a == 1 && b == 2 && c == 3) return 1;
        //        if (a == 2 && b == 4 && c == 5) return 1;
        //    }
        //    else if (layer == 1)
        //    {
        //        if (a == 0 && b == 0 && c == 1) return 1;
        //    }
        //    return 0;
        //}
        private static Func<int[], int[], int[], int> MulPoly(int layer)
        {
            return (int[] a, int[] b, int[] c) =>
            {
                int s = 0;
                if (layer == 2)
                {
                    s += (1 - a[0]) * a[1] * (1 - b[0]) * b[1] * (1 - b[2]) * (1 - c[0]) * c[1] * c[2];
                    s += a[0] * (1 - a[1]) * b[0] * (1 - b[1]) * (1 - b[2]) * c[0] * (1 - c[1]) * c[2];
                }
                else if (layer == 1)
                {
                    s += (1 - a[0]) * (1 - b[0]) * (1 - b[1]) * (1 - c[0]) * c[1];
                }
                else if (layer == 0)
                {
                }
                return s;
            };
        }

        class Node
        {
            public int? value;
            public int sign;        // 0: + , 1: -
            public Node left;
            public Node right;

            public Node()
            {
                this.value = null;
                this.left = null;
                this.right = null;
            }

            public Node(int value)          // input node
            {
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

            public Prover(int layer, int[] gateNum, int[] bitsLen, int mod)
            {
                this.layer = layer;
                this.gateNum = gateNum;
                this.bitsLen = bitsLen;
                this.mod = mod;
                funs = new Func<int[], int[], int[], int>[layer];
                Vs = new Func<int[], int>[layer + 1];
                for (int i = 0; i < layer; i++)
                {
                    funs[i] = make_f(i);
                    Vs[i] = make_V(gateNum[i], i);
                }
                Vs[layer] = make_V(gateNum[layer], layer);
            }

            public int W(int now_lawer, int index)
            {
                if (now_lawer == 3)
                {
                    int[] values = { 1, 2, 3, 4, 5, 6, 7, 8 };  //input
                    return values[index];
                }
                else if (now_lawer == 2)
                {
                    int[] values = { 3, 12, 30, 15 };
                    return values[index];
                }
                else if (now_lawer == 1)
                {
                    int[] values = { 36, 45 };
                    return values[index];
                }
                else if (now_lawer == 0)
                {
                    int[] values = { 81 };                      //output
                    return values[index];
                }
                return -1;
            }

            public Func<int[], int> make_V(int gateNum, int layer)          //邏輯要改
            {
                return (int[] z) =>
                {
                    int s = 0;
                    for (int i = 0; i < gateNum; i++)
                    {
                        if (z.Length == 1)
                        {
                            if (i == 0) s += W(layer, i) * (1 - z[0]);
                            else if (i == 1) s += W(layer, i) * z[0];
                        }
                        else if (z.Length == 2)
                        {
                            if (i == 0) s += W(layer, i) * (1 - z[0]) * (1 - z[1]);
                            else if (i == 1) s += W(layer, i) * (1 - z[0]) * z[1];
                            else if (i == 2) s += W(layer, i) * z[0] * (1 - z[1]);
                            else if (i == 3) s += W(layer, i) * z[0] * z[1];
                        }
                        else if (z.Length == 3)
                        {
                            if (i == 0) s += W(layer, i) * (1 - z[0]) * (1 - z[1]) * (1 - z[2]);
                            else if (i == 1) s += W(layer, i) * (1 - z[0]) * (1 - z[1]) * z[2];
                            else if (i == 2) s += W(layer, i) * (1 - z[0]) * z[1] * (1 - z[2]);
                            else if (i == 3) s += W(layer, i) * (1 - z[0]) * z[1] * z[2];
                            else if (i == 4) s += W(layer, i) * z[0] * (1 - z[1]) * (1 - z[2]);
                            else if (i == 5) s += W(layer, i) * z[0] * (1 - z[1]) * z[2];
                            else if (i == 6) s += W(layer, i) * z[0] * z[1] * (1 - z[2]);
                            else if (i == 7) s += W(layer, i) * z[0] * z[1] * z[2];
                        }
                    }
                    return Mod(s, mod);
                };
            }

            public Func<int[], int[], int[], int> make_f(int layer)
            {
                return (int[] a, int[] b, int[] c) =>
                {
                    int s = 0;
                    var nextLayerV = make_V(gateNum[layer + 1], layer + 1);
                    s += AddPoly(layer)(a, b, c) * (nextLayerV(b) + nextLayerV(c));
                    s += MulPoly(layer)(a, b, c) * (nextLayerV(b) * nextLayerV(c));
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

            public Func<int, int> make_q(int layer, int[] fixed_var)
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

            public Func<int, int> claimed_D()
            {
                return (int z) =>
                {
                    return Vs[0]( new int[] { z } );
                };
            }
        }

        class Verifier
        {
            private Random rand = new Random();
            private int mod;

            public Verifier(int mod)
            {
                this.mod = mod;
            }

            public int pickRandom()
            {
                return rand.Next(mod);
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

            for (int i = 0; i < layer; i++)                                 // gate
            {
                while (true)
                {
                    if (i == 0) Console.Write("(output) ");
                    else if (i == layer - 1) Console.Write("(input) ");
                    Console.Write($"layer {i} = ");
                    string n = Console.ReadLine().Trim();
                    if (i == layer-1)
                    {
                        string[] parts = n.Split(',');
                        if (parts == null)
                        {
                            Console.WriteLine("Please enter a valid input.");
                            continue;
                        }
                        if (parts.All(p => int.TryParse(p, out _)))
                        {
                            for (int j = 0; j < parts.Length; j++)
                            {
                                circuit[i][j] = new Node(int.Parse(parts[j]));
                            }
                            break;
                        }
                    }
                    else if (n.Distinct().OrderBy(x => x).SequenceEqual(new[] { '0', '1' }))
                    {
                        circuit[i] = new Node[n.Length];
                        for (int j = 0; j < n.Length; j++)
                        {
                            circuit[i][j] = new Node();
                            if (n[j] == '0') circuit[i][j].set_sign(0);
                            else if (n[j] == '1') circuit[i][j].set_sign(1);
                        }
                        break;
                    }
                    Console.WriteLine("Please enter a valid input.");
                }
            }

            for (int i = 0; i < layer-1; i++)                           // connect layers
            {
                while (true)
                {
                    bool wrong = false;
                    Console.Write($"Connect layer {i} to layer {i + 1} : ");
                    string n = Console.ReadLine().Trim();
                    string[] parts = n.Split('@');
                    string[][] nodes = new string[parts.Length][];
                    for (int j = 0; j < parts.Length; j++) nodes[j] = parts[j].Split(',');
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

            for (int i = layer - 1; i >= 0; i--)                           // calculate values
            {
                for (int j = 0; j < circuit[i].Length; j++)
                {
                    circuit[i][j].calculate_value();
                }
            }


            //int mod = 83;                                                               //初始化電路
            //int layer = 3;
            //int[] gateNum = { 1, 2, 4, 8 };
            //int[] bitsLen = new int[gateNum.Length];
            //for (int i = 0; i < gateNum.Length; i++)
            //{
            //    if (gateNum[i] == 1)
            //    {
            //        bitsLen[i] = 1;
            //        continue;
            //    }
            //    bitsLen[i] = (int)Math.Ceiling(Math.Log(gateNum[i], 2));

            //    Console.WriteLine($"bitLen {i}:" + bitsLen[i]);

            //}

            Prover prover = new Prover(layer, gateNum, bitsLen, mod);                   //建立P,V
            Verifier verifier = new Verifier(mod);

            //建立需要的變數
            int[] fixed_var = new int[bitsLen[0]];
            for (int i = 0; i < fixed_var.Length; i++) fixed_var[i] = verifier.pickRandom();
            int random_var;
            //Func<int, int> answer_poly = prover.claimed_D();
            var claimed_poly = prover.claimed_D();
            int claimed;
            int midterm;
            Func<int, int[]> l_poly;



            Console.WriteLine("answer: " + prover.claimed_D()(0));
            //for (int i = 0; i < fixed_var.Length; i++) Console.WriteLine("P: Claimed answer_poly: " + prover.claimed_D()(IntToBinary(i, fixed_var.Length)));       //P 宣稱答案
            
            // 第一輪開始可以是多個 fixed_var 填入 claimed_poly 計算，或許要用 l()
            claimed = claimed_poly(fixed_var[0]);


            for (int now_layer = 0; now_layer < layer; now_layer++)
            {
                //fixed_var[0] = verifier.pickRandom();
                //Console.WriteLine($"V: Fixed var for layer {now_layer}: " + fixed_var[0]);

                
                //Console.WriteLine($"P: claimed_poly{now_layer}({fixed_var[0]}) = " + claimed);
                Console.WriteLine(" sum check ");
                for (int i = 0; i < bitsLen[now_layer + 1] * 2 ; i++)           //sum check
                {
                    var G = prover.make_G(fixed_var, now_layer);
                    Console.WriteLine($"P: send G{i}");
                    Console.WriteLine($"V: Verifying G{i}(0) + G{i}(1) ?= claimed");

                    //Console.WriteLine($" G(0): {G(0)}, G(1): {G(1)} ");

                    midterm = Mod(G(0) + G(1), mod);
                    if (midterm != claimed) { Console.WriteLine("V: sum check failed"); return; }
                    int s = verifier.pickRandom();
                    Console.WriteLine($"V: pick s{i} = {s}");
                    Array.Resize(ref fixed_var, fixed_var.Length + 1);
                    fixed_var[fixed_var.Length - 1] = s;
                    claimed = G(s);
                    Console.WriteLine($"P: claimed G{i}(s{i}) = {claimed}");

                    if (i == bitsLen[now_layer + 1] * 2 - 1)
                    {
                        claimed_poly = prover.make_q(now_layer, fixed_var);
                        Console.WriteLine("P: send claimed_poly" + (now_layer + 1));
                        int[] a = fixed_var.Take(bitsLen[now_layer]).ToArray();
                        int[] b = fixed_var.Skip(bitsLen[now_layer]).Take(bitsLen[now_layer + 1]).ToArray();
                        int[] c = fixed_var.Skip(bitsLen[now_layer] + bitsLen[now_layer + 1]).Take(bitsLen[now_layer + 1]).ToArray();
                        Console.WriteLine("V: sum check final check ");
                        midterm = Mod((AddPoly(now_layer)(a, b, c) * (claimed_poly(0) + claimed_poly(1))) + (MulPoly(now_layer)(a, b, c) * (claimed_poly(0) * claimed_poly(1))), mod);

                        //Console.WriteLine("midterm: " + midterm);

                        if (claimed != midterm) { Console.WriteLine("V: final check failed"); return; }
                        //Array.Resize(ref fixed_var, 1);
                        Console.WriteLine(" sum check passed ");

                        random_var = verifier.pickRandom();
                        claimed = claimed_poly(random_var);
                        l_poly  = prover.make_l(now_layer, fixed_var);
                        Array.Resize(ref fixed_var, bitsLen[now_layer + 1]);
                        for (int j = 0; j < fixed_var.Length; j++)
                        {
                            fixed_var[j] = l_poly(random_var)[j];

                            Console.WriteLine(now_layer);
                            Console.WriteLine($" fixed_var {j}: " + fixed_var[j]);

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


//layer0: <0> (+) 36+45 = 81
//layer1: <0> (*) 3*12 = 36, <1> (+) 30+15 = 45
//layer2: <00> (+) 1+2 = 3, <01> (*) 3*4 = 12, <10> (*) 5*6 = 30, <11> (+) 7+8 = 15
//layer3: <000> 1, <001> 2, <010> 3, <011> 4, <100> 5, <101> 6, <110> 7, <111> 8
