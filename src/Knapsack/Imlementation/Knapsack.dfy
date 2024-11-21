include "../../Math.dfy"
include "../../ContainersOps.dfy"
include "VA.dfy"
include "Input.dfy"

/*
	El método ComputeSolution toma un input y calcula la solución óptima mediante la llamada a un método de 
	vuelta atrás (KnapsackVA).
 */
method ComputeSolution(input: Input) returns (solution: Solution) //llamarlo bs
	requires input.Model().Valid()

	ensures solution.Valid(input)
	ensures solution.Optimal(input)
	
{
	// assert solution.Valid(input) by {
	// 	assert solution.k == solution.itemsAssign.Length;
    // 	assert solution.Partial(input);
	// }

	// assert solution.Model().Optimal(input.Model()) by {
	// 	assert input.Valid(); //ok
	// 	assert solution.Valid(input); 
	// }

	var size := input.items.Length;

	// Construir partial solution (ps)
	var itemsAssign: array<bool> := new bool[size](i => false);
  	var totalValue: real := 0.0;
  	var totalWeight: real := 0.0;
  	var k: int := 0;
	var ps := new Solution(itemsAssign, totalValue, totalWeight, k);
	ghost var oldpsmodel := ps.Model();
	assert ps.Partial(input) by {
		assert ps.Model().Partial(input.Model()); // ok
	}

	// Construir best solution (bs)
	var itemsAssign2: array<bool> := new bool[size](i => false);
  	var totalValue2: real := 0.0;
  	var totalWeight2: real := 0.0;
  	var k2: int := size;
	var bs := new Solution(itemsAssign2, totalValue2, totalWeight2, k2);
	ghost var oldbsmodel := bs.Model();

	assert bs.Valid(input) by {
		bs.Model().SumOfFalsesEqualsZero(input.Model());	
	}
	KnapsackVA(input, ps, bs);
	solution := bs;

	
	//Ver las postcondiciones de KnapsackVA corresponden con las postcondiciones de ComputeSolution:	
	// 1) La primera postcondición es trivial, si conseguimos verificar que bs.Valid() es verdadero, solution también lo será (hacemos solution := bs)


	assert bs.Model().Optimal(input.Model()) by {
		forall otherSolution: SolutionData | otherSolution.Valid(input.Model()) 
		ensures otherSolution.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items) {
			assert otherSolution.Extends(ps.Model());			
		}
	}
}


method Main() {

	// Entrada del problema
	var item1 := new Item(8.0, 1.0);
	var item2 := new Item(2.0, 2.0);
	var item3 := new Item(4.0, 3.0);
	assert item1.Valid() && item2.Valid() && item3.Valid();

	var items: array<Item> := new Item[3][item1, item2, item3]; // objetos que hay
	var maxWeight: real := 8.0; // peso máximo de la mochila

	var input := new Input(items, maxWeight);
	assert input.Valid();

	// Resolución del problema
	var bs := ComputeSolution(input);
	print "The bag admits a weight of: ", input.maxWeight, "\n";
	print "The maximum value achievable is: ", bs.totalValue, "\n";
	print "By putting inside:\n";
	for i := 0 to input.items.Length {
		if (bs.itemsAssign[i]) {
			print "Item ", i," with weight: ", input.items[i].weight, " and value: ", input.items[i].value;
		}
	}
	print "\nTotal weight: ", bs.totalWeight, "\n";
}
