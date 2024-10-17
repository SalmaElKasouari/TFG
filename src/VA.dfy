include "Solution.dfy"
//include "Input.dfy"

/*
Método general que llama a la vuelta atrás. Se implementará de manera que el árbol de exploraciín sea un árbol 
binario, donde las etapas son los objetos que debemos tratar y las ramas representan la decisión de coger el objeto.

Tenemos ps (partial solution) y bs (best solution) de entrada y salida. El ps se irá rellenando con la vuelta atrás,
el bs guardará la mejor solución encontrada hasta el momento. Este último estará incializado a ceros, debido a que
tratamos con un problema de maximización.

*/

method KnapsackVA(items: array<Item>, maxWeight: real, ps: Solution, bs: Solution) returns (bestValue: real)
  modifies ps, ps.itemsAssign, bs

  //Precondiciones
  requires 0 <= ps.k < ps.itemsAssign.Length

  requires ps.Valid(items, maxWeight) //en lugar de esto
  //requires Input(items, maxWeight).Model(ps).Valid(Model(ps).) //se pondría algo como esto

  requires bs.Valid(items, maxWeight)


  //PostcondicionesS
  ensures ps.Valid(items, maxWeight) //usar input
  ensures bs.Valid(items, maxWeight) //usar input

  ensures ps.itemsAssign == old(ps.itemsAssign)
  ensures ps.k == old(ps.k)
  ensures ps.totalValue == old(ps.totalValue)
  ensures ps.totalWeight == old(ps.totalWeight)

  ensures bs.totalValue >= old(bs.totalValue)
  ensures bs.totalValue >= ps.totalValue
  ensures bs.totalValue == old(bs.totalValue) || bs.totalValue >= ps.totalValue
  ensures bs.k <= items.Length
  ensures bs.totalValue >= old(bs.totalValue)
  ensures bs.totalWeight >= old(bs.totalWeight)
  ensures bs.k == items.Length

  decreases ps.itemsAssign.Length - ps.k + 1

{

  // RAMA SI COGEMOS EL OBJETO
  ps.itemsAssign[ps.k] := true;
  ps.totalWeight := ps.totalWeight + items[ps.k].weight; // marcar
  ps.totalValue := ps.totalValue + items[ps.k].value; // marcar
  ps.k := ps.k + 1; // marcar
  if ps.Valid(items, maxWeight) {
    if (ps.k == items.Length) { // hemos tratado todos los objetos
      if (ps.totalValue > bs.totalValue) {
        bs.totalValue := ps.totalValue;
        bs.totalWeight := ps.totalWeight;
        bs.itemsAssign := ps.itemsAssign;
        bs.k := ps.k;
      }
    }
    else { // la solución es completable --> llamada recursiva
      bestValue := KnapsackVA(items, maxWeight, ps, bs);
    }
  }
  ps.k := ps.k - 1; // desmarcar
  ps.totalWeight := ps.totalWeight - items[ps.k].weight; //desmarcar
  ps.totalValue := ps.totalValue - items[ps.k].value; // desmarcar


  // RAMA NO COGEMOS EL OBJETO
  ps.itemsAssign[ps.k] := false;
  ps.k := ps.k + 1;
  if (ps.k == items.Length) { // hemos tratado todos los objetos
    if (ps.totalValue > bs.totalValue) {
      bs.totalValue := ps.totalValue;
      bs.totalWeight := ps.totalWeight;
      bs.itemsAssign := ps.itemsAssign;
      bs.k := ps.k;
    }
  }
  else { // la solución es completable --> llamada recursiva
    bestValue := KnapsackVA(items, maxWeight, ps, bs);
  }
  ps.k := ps.k - 1;

  bestValue := bs.totalValue;
}


