include "Math.dfy"
include "ContainersOps.dfy"

//Notas sobre los tipos: usar clases en codigo y datatypes en especificacion:

//1. en la implementacion usar una clase Solution para la solucion
// ¿usamos tambien una clase InputData en lugar del datatype Object?

//2. en la especificación usamos secuencias y datatypes 
//Object , que corresponderia a InputData
//Knapsack extendido con mas cosas que correspondería a Solution

//A nivel de especificación tenemos estos datatype
datatype Object = Object(weight: real, value: real)  
datatype Knapsack = Knapsack(objectsSelected: seq<bool>, maxWeight: real)


ghost predicate ValidInstance(objects: seq<Object>, maxWeight: real)
{       
	|objects| > 0
	 && maxWeight >= 0.0
	 && forall i: nat | i < |objects| :: objects[i].weight > 0.0 && objects[i].value > 0.0
	 
}

//Cambiar a reales en lugar de naturales y mejorar los nombres. Reales hecho.
ghost function TotalWeight(objects: seq<Object>, objEndIdx: nat, objectsAssign: seq<bool>): real
	requires objEndIdx <= |objects|
	requires objEndIdx <= |objectsAssign|
{
	var objSelected: seq<Object> := selectSeq(objects, objectsAssign, 0, objEndIdx);
	var numSelected: nat := |objSelected|;
	var weightsSelected: seq<real> := mapSeq(objSelected, (obj: Object) => obj.weight, 0, numSelected);
	sum_real(weightsSelected, 0, numSelected)
}

ghost function SolutionValue(objects: seq<Object>, objEndIdx: nat, objectsAssign: seq<bool>): (o: real)
	requires objEndIdx <= |objects|
	requires objEndIdx <= |objectsAssign|
{
	var objSelected: seq<Object> := selectSeq(objects, objectsAssign, 0, objEndIdx);
	var numSelected: nat := |objSelected|;
	var valuesSelected: seq<real> := mapSeq(objSelected, (obj: Object) => obj.value, 0, numSelected);
	sum_real(valuesSelected, 0, numSelected)
}

ghost predicate ValidSolution(objects: seq<Object>, objEndIdx: nat, maxWeight: real, objectsAssign: seq<bool>)
	requires objEndIdx <= |objects|
	requires objEndIdx <= |objectsAssign|
{
	TotalWeight(objects, objEndIdx, objectsAssign) <= maxWeight
}

ghost predicate OptimalSolution(objects: seq<Object>, objEndIdx: nat, availableWeight: real, objectsAssign: seq<bool>)
	requires ValidInstance(objects,availableWeight)
	requires objEndIdx <= |objects|
	requires objEndIdx <= |objectsAssign|
	requires ValidSolution(objects, objEndIdx, availableWeight, objectsAssign)
{
	forall otherSolution: seq<bool> | objEndIdx <= |otherSolution| && ValidSolution(objects, objEndIdx, availableWeight, otherSolution) :: SolutionValue(objects, objEndIdx, otherSolution) <= SolutionValue(objects, objEndIdx, objectsAssign)
}


method {:axiom} ComputeSolution(objects: array<Object>, maxWeight: real) returns (maxValue: real, objectsAssign: array<bool>)
	requires ValidInstance(objects[..],maxWeight)

	ensures objectsAssign.Length == objects.Length
	ensures ValidSolution(objects[..], objects.Length, maxWeight, objectsAssign[..])
	ensures SolutionValue(objects[..], objects.Length, objectsAssign[..]) == maxValue
	ensures OptimalSolution(objects[..], objects.Length, maxWeight, objectsAssign[..])


method Main() {
	var objects: array<Object> := new Object[3][
		Object(8.0, 1.0),
		Object(2.0, 2.0),
		Object(4.0, 3.0)
		];

	var maxWeight: real := 8.0;

	var maxValue, objectsAssign := ComputeSolution(objects, maxWeight);

	print "The bag admits a weight of: ", maxWeight, "\n";
	print "The maximum value achievable is: ", maxValue, "\n";
	print "By putting inside:\n";

	var totalWeight := 0.0;

	for i: int := 0 to objectsAssign.Length
	{
		if(objectsAssign[i]) {
			print "Object ", i, " with weight ", objects[i].weight, " and value ", objects[i].value, "\n";
			totalWeight := totalWeight + objects[i].weight;
		}
	}

	print "\nTotal weight: ", totalWeight, "\n";
}
