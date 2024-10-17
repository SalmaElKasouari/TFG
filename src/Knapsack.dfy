include "Math.dfy"
include "ContainersOps.dfy"
include "Especificacion.dfy"
include "Solution.dfy"
include "VA.dfy"

ghost predicate ValidInstance(items: seq<ItemData>, maxWeight: real)
{       
	|items| > 0
	 && maxWeight >= 0.0
	 && forall i: nat | i < |items| :: items[i].weight > 0.0 && items[i].value > 0.0
	 
}

//Cambiar a reales en lugar de naturales y mejorar los nombres. Reales hecho.
ghost function TotalWeight(items: seq<ItemData>, itemEndIdx: nat, itemsAssign: seq<bool>): real
	requires itemEndIdx <= |items|
	requires itemEndIdx <= |itemsAssign|
{
	var objSelected: seq<ItemData> := selectSeq(items, itemsAssign, 0, itemEndIdx);
	var numSelected: nat := |objSelected|;
	var weightsSelected: seq<real> := mapSeq(objSelected, (obj: ItemData) => obj.weight, 0, numSelected);
	sum_real(weightsSelected, 0, numSelected)
}

ghost function SolutionValue(items: seq<ItemData>, itemEndIdx: nat, itemsAssign: seq<bool>): (o: real)
	requires itemEndIdx <= |items|
	requires itemEndIdx <= |itemsAssign|
{
	var objSelected: seq<ItemData> := selectSeq(items, itemsAssign, 0, itemEndIdx);
	var numSelected: nat := |objSelected|;
	var valuesSelected: seq<real> := mapSeq(objSelected, (obj: ItemData) => obj.value, 0, numSelected);
	sum_real(valuesSelected, 0, numSelected)
}

ghost predicate ValidSolution(items: seq<ItemData>, itemEndIdx: nat, maxWeight: real, itemsAssign: seq<bool>)
	requires itemEndIdx <= |items|
	requires itemEndIdx <= |itemsAssign|
{
	TotalWeight(items, itemEndIdx, itemsAssign) <= maxWeight
}

ghost predicate OptimalSolution(items: seq<ItemData>, itemEndIdx: nat, availableWeight: real, itemsAssign: seq<bool>)
	requires ValidInstance(items,availableWeight)
	requires itemEndIdx <= |items|
	requires itemEndIdx <= |itemsAssign|
	requires ValidSolution(items, itemEndIdx, availableWeight, itemsAssign)
{
	forall otherSolution: seq<bool> | itemEndIdx <= |otherSolution| && ValidSolution(items, itemEndIdx, availableWeight, otherSolution) :: SolutionValue(items, itemEndIdx, otherSolution) <= SolutionValue(items, itemEndIdx, itemsAssign)
}


method {:axiom} ComputeSolution(items: array<ItemData>, maxWeight: real) returns (maxValue: real, itemsAssign: array<bool>)
	requires ValidInstance(items[..],maxWeight)

	ensures itemsAssign.Length == items.Length
	ensures ValidSolution(items[..], items.Length, maxWeight, itemsAssign[..])
	ensures SolutionValue(items[..], items.Length, itemsAssign[..]) == maxValue
	ensures OptimalSolution(items[..], items.Length, maxWeight, itemsAssign[..])


method Main() {
	//Descripción del problema
	var items: array<ItemData> := new ItemData[3][
		ItemData(8.0, 1.0),
		ItemData(2.0, 2.0),
		ItemData(4.0, 3.0)
		];

	var maxWeight: real := 8.0;

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

	//Quiero que sea void pero method pide un retorno
	var maxValue := KnapsackVA(items, maxWeight, ps, bs); //problema, se espera array<Item> no de array<ItemData>

	print "The bag admits a weight of: ", maxWeight, "\n";
	print "The maximum value achievable is: ", maxValue, "\n";
	print "By putting inside:\n";

	print "\nTotal weight: ", bs.totalWeight, "\n";
}
