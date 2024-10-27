include "../../Math.dfy"
include "../../ContainersOps.dfy"
include "VA.dfy"
include "Input.dfy"


method {:axiom} ComputeSolution(input: Input) returns (solution: Solution)
	requires input.Valid()

	ensures solution.Valid(input)
	ensures solution.Optimal(input)

method Main() {

	// Entrada del problema

	var item1 := new Item(8.0, 1.0);
	var item2 := new Item(2.0, 2.0);
	var item3 := new Item(4.0, 3.0);

	var items: array<Item> := new Item[3][item1, item2, item3]; // objetos que hay
	var maxWeight: real := 8.0; // peso máximo de la mochila

	var input := new Input(items, maxWeight);


	// Elementos para resolver el problema

	// Partial solution (ps)
	var itemsAssign: array<bool> := new bool[3][
		false,
		false,
		false
		];
  	var totalValue: real := 0.0;
  	var totalWeight: real := 0.0;
  	var k: int := 0;
	var ps := new Solution(itemsAssign, totalValue, totalWeight, k);

	// Best solution (bs)
	var itemsAssign2: array<bool>:= new bool[3][
		false,
		false,
		false
		];
  	var totalValue2: real := 0.0;
  	var totalWeight2: real := 0.0;
  	var k2: int := 0;
	var bs := new Solution(itemsAssign2, totalValue2, totalWeight2, k2);

	//KnapsackVA(input, ps, bs);

	print "The bag admits a weight of: ", maxWeight, "\n";
	print "The maximum value achievable is: ", bs.totalValue, "\n";
	print "By putting inside:\n";

	print "\nTotal weight: ", bs.totalWeight, "\n";
}
