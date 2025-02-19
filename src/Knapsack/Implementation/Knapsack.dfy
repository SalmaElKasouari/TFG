/*---------------------------------------------------------------------------------------------------------------------

Este fichero incluye la resolución del problema de la mochila.

Estructura del fichero:

  Métodos:
	- ComputeSolution: encuentra una solución óptima que resuelve el problema mediante al algoritmo de vuelta atrás.
  	- Main: ejecuta el programa principal y muestra la solución.

---------------------------------------------------------------------------------------------------------------------*/

include "../../Math.dfy"
include "../../ContainersOps.dfy"
include "VA.dfy"
include "Input.dfy"

/* Métodos */

/*
Método: dado un input, encuentra la solución óptima mediante la llamada a un método de vuelta atrás (KnapsackVA)
implementado en VA.dfy. Se construyen dos soluciones:
	- Una solución parcial (ps): va construyendo la solución actual (decide las asignaciones de los objetos).
	- Una mejor soluión (bs): almacena la mejor solución encontrada hasta el momento. 
Ambas soluciones se inicializan con el array de asignaciones a falsos.
//
Verificación: se asegura que bs (la solución que se encuentra) es tanto válida como óptima:
	- bs.Valid(input): mediante la poscondición en VA que asegura que bs es válida.
	- bs.Optimal (input): mediante varias poscondiciones en VA que aseguran que bs es óptima.
*/
method ComputeSolution(input: Input) returns (bs: Solution) //llamarlo bs
	requires input.Valid()
	ensures bs.Valid(input)
	ensures bs.Optimal(input)	
{
	var n := input.items.Length;

	/* Construimos una solución parcial (ps) */
	var ps_itemsAssign: array<bool> := new bool[n](i => false);
  	var ps_totalValue: real := 0.0;
  	var ps_totalWeight: real := 0.0;
  	var ps_k: int := 0;
	var ps := new Solution(ps_itemsAssign, ps_totalValue, ps_totalWeight, ps_k);
	ghost var oldpsmodel := ps.Model();
	assert ps.Partial(input) by {
		assert ps.Model().Partial(input.Model());
	}

	/* Construimos una solución mejor (bs) */
	var bs_itemsAssign: array<bool> := new bool[n](i => false);
  	var bs_totalValue: real := 0.0;
  	var bs_totalWeight: real := 0.0;
  	var bs_k: int := n;
	bs := new Solution(bs_itemsAssign, bs_totalValue, bs_totalWeight, bs_k);
	ghost var oldbsmodel := bs.Model();

	assert bs.Valid(input) by {
		bs.Model().SumOfFalsesEqualsZero(input.Model());	
	}

	KnapsackVA(input, ps, bs);

	
	/* Primera postcondición: bs.Valid(input) 
		Se verifica gracias a la poscondición en VA que asegura que bs es válida.
	*/

	/* Segunda postcondición: bs.Optimal(input) 
		Se verifica gracias a varias poscondiciones en VA que aseguran que bs es óptima.
	*/
	assert bs.Optimal(input) by {
		forall s: SolutionData | s.Valid(input.Model()) 
		ensures s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items) {
			assert s.Extends(ps.Model());			
		}
	}
}

/*
Método: main que ejecuta el programa principal resolviendo el problema de la mochila con un conjunto de objetos 
y un peso máximo definidos.
*/
method Main() {

	/* Objetos que tenemos a nuestra disposición */
	var item1 := new Item(8.0, 1.0);
	var item2 := new Item(2.0, 2.0);
	var item3 := new Item(4.0, 3.0);
	var items: array<Item> := new Item[3][item1, item2, item3];
	
	
	/* Peso máximo de la mochila */
	var maxWeight: real := 8.0;

	/* Generar la entrada del problema */
	var input := new Input(items, maxWeight);

	/* Resolver el problema */
	var bs := ComputeSolution(input);

	/* Imprimir la solución */
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
