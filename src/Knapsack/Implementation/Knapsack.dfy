include "../../Math.dfy"
include "../../ContainersOps.dfy"
include "VA.dfy"
include "Input.dfy"

/*
	El método ComputeSolution toma un input y calcula la solución óptima mediante la llamada a un método de 
	vuelta atrás (KnapsackVA).
 */
method ComputeSolution(input: Input) returns (bs: Solution) //llamarlo bs
	requires input.Valid()

	ensures bs.Valid(input)
	ensures bs.Optimal(input)
	
{
	var size := input.items.Length;

	// Construir partial solution (ps)
	var ps_itemsAssign: array<bool> := new bool[size](i => false);
  	var ps_totalValue: real := 0.0;
  	var ps_totalWeight: real := 0.0;
  	var ps_k: int := 0;
	var ps := new Solution(ps_itemsAssign, ps_totalValue, ps_totalWeight, ps_k);
	ghost var oldpsmodel := ps.Model();
	assert ps.Partial(input) by {
		assert ps.Model().Partial(input.Model());
	}

	// Construir best solution (bs)
	var bs_itemsAssign: array<bool> := new bool[size](i => false);
  	var bs_totalValue: real := 0.0;
  	var bs_totalWeight: real := 0.0;
  	var bs_k: int := size;
	bs := new Solution(bs_itemsAssign, bs_totalValue, bs_totalWeight, bs_k);
	ghost var oldbsmodel := bs.Model();

	assert bs.Valid(input) by {
		bs.Model().SumOfFalsesEqualsZero(input.Model());	
	}
	KnapsackVA(input, ps, bs);

		
	// 1) La primera postcondición es trivial, ya que hay una poscondición en VA que asegura que bs es valid

	/*
	* Demostración de bs.Optimal() a partir de las otras poscondiciones sobre bs que encontramos en VA
	*/
	assert bs.Optimal(input) by {
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
