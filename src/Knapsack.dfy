include "Math.dfy"
include "ContainersOps.dfy"

//Notas sobre los tipos: usar clases en codigo y datatypes en especificacion:

//1. en la implementacion usar una clase Solution para la solucion
// ¿usamos tambien una clase InputData en lugar del datatype Object?

//2. en la especificación usamos secuencias y datatypes 
//Object , que corresponderia a InputDara
//Knapsack extendido con mas cosas que correspondería a Solution

//A nivel de especificación tenemos estos datatype
datatype Object = Object(weight: nat, value: real)  
datatype Knapsack = Knapsack(objectsSelected: seq<bool>, maxWeight: nat) //poner real a los pesos


ghost predicate validInstance(objects: seq<Object>, maxWeight: int)
{       |objects| > 0
	 && maxWeight >= 0
	 && forall i: nat | i < |objects| :: objects[i].weight > 0 && objects[i].value > 0.0
	 
}

//Cambiar a reales en lugar de naturales y mejorar los nombres 
ghost function Weight(objects: seq<Object>, objEndIdx: nat, v: seq<bool>): nat
	requires objEndIdx <= |objects|
	requires objEndIdx <= |v|
{
	var objSel: seq<Object> := selectSeq(objects, v, 0, objEndIdx);
	var numObjSel: nat := |objSel|;
	var weightsSel: seq<nat> := mapSeq(objSel, (obj: Object) => obj.weight, 0, numObjSel);
	sumNat(weightsSel, 0, numObjSel); 
	sum(weightsSel, 0, numObjSel)
}

ghost function solutionValue(objects: seq<Object>, objEndIdx: nat, v: seq<bool>): (o: real)
	requires objEndIdx <= |objects|
	requires objEndIdx <= |v|
{
	var objSel: seq<Object> := selectSeq(objects, v, 0, objEndIdx);
	var numObjSel: nat := |objSel|;
	var valuesSel: seq<real> := mapSeq(objSel, (obj: Object) => obj.value, 0, numObjSel);
	sum_real(valuesSel, 0, numObjSel)
}

ghost predicate validSolution(objects: seq<Object>, objEndIdx: nat, maxWeight: nat, v: seq<bool>)
	requires objEndIdx <= |objects|
	requires objEndIdx <= |v|
{
	Weight(objects, objEndIdx, v) <= maxWeight
}

ghost predicate optimalSolution(objects: seq<Object>, objEndIdx: nat, availableWeight: nat, v: seq<bool>)
	requires validInstance(objects,availableWeight)
	requires objEndIdx <= |objects|
	requires objEndIdx <= |v|
	requires validSolution(objects, objEndIdx, availableWeight, v)
{
	forall otherSolution: seq<bool> | objEndIdx <= |otherSolution| && validSolution(objects, objEndIdx, availableWeight, otherSolution) :: solutionValue(objects, objEndIdx, otherSolution) <= solutionValue(objects, objEndIdx, v)
}


method {:axiom} computeSolution(objects: array<Object>, maxWeight: int) returns (maxValue: real, objectAssign: array<bool>)
	requires validInstance(objects[..],maxWeight)

	ensures objectAssign.Length == objects.Length
	ensures validSolution(objects[..], objects.Length, maxWeight, objectAssign[..])
	ensures solutionValue(objects[..], objects.Length, objectAssign[..]) == maxValue
	ensures optimalSolution(objects[..], objects.Length, maxWeight, objectAssign[..])


method Main() {
	var objects: array<Object> := new Object[3][
		Object(8, 1.0),
		Object(2, 2.0),
		Object(4, 3.0)
		];

	var maxWeight: int := 8;

	var maxValue, objectAssign := computeSolution(objects, maxWeight);

	print "The bag admits a weight of: ", maxWeight, "\n";
	print "The maximum value achievable is: ", maxValue, "\n";
	print "By putting inside:\n";

	var totalWeight := 0;

	for i: int := 0 to objectAssign.Length
	{
		if(objectAssign[i]) {
			print "Object ", i, " with weight ", objects[i].weight, " and value ", objects[i].value, "\n";
			totalWeight := totalWeight + objects[i].weight;
		}
	}

	print "\nTotal weight: ", totalWeight, "\n";
}
