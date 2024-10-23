include "Solution.dfy"
include "Input.dfy"

/*
Método general que llama a la vuelta atrás. Se implementará de manera que el árbol de exploraciín sea un árbol 
binario, donde las etapas son los objetos que debemos tratar y las ramas representan la decisión de coger el objeto.

Tenemos ps (partial solution) y bs (best solution) de entrada y salida. El ps se irá rellenando con la vuelta atrás,
el bs guardará la mejor solución encontrada hasta el momento. Este último estará incializado a ceros, debido a que
tratamos con un problema de maximización.

*/

method KnapsackVA(input: Input, ps: Solution, bs: Solution)
  modifies ps, ps.itemsAssign, bs

  //Precondiciones
  requires input.Valid()
  requires 0 <= ps.k < ps.itemsAssign.Length

  requires ps.Valid(input)  
  requires bs.Valid(input)


  //Postcondiciones
  ensures ps.Valid(input)
  ensures bs.Valid(input)

  ensures ps.itemsAssign == old(ps.itemsAssign)
  ensures ps.k == old(ps.k)
  ensures ps.totalValue == old(ps.totalValue)
  ensures ps.totalWeight == old(ps.totalWeight)

  ensures bs.totalValue >= old(bs.totalValue)
  ensures bs.totalValue >= ps.totalValue
  ensures bs.totalValue == old(bs.totalValue) || bs.totalValue >= ps.totalValue
  ensures bs.k <= input.items.Length
  ensures bs.totalValue >= old(bs.totalValue)
  ensures bs.totalWeight >= old(bs.totalWeight)
  ensures bs.k == input.items.Length

  decreases ps.itemsAssign.Length - ps.k + 1

{
  // Asertos para comprobar que sean valid las solutions
  assert ps.Valid(input);
  assert bs.Valid(input);

  // RAMA SI COGEMOS EL OBJETO
  ps.itemsAssign[ps.k] := true;
  ps.totalWeight := ps.totalWeight + input.items[ps.k].weight; // marcar
  ps.totalValue := ps.totalValue + input.items[ps.k].value; // marcar
  ps.k := ps.k + 1; // marcar

  assert input.Valid(); //ok
  assert ps.Model().TotalWeight(input.Model().items) == ps.totalWeight; //ver
  assert ps.Model().Value(input.Model().items) == ps.totalValue; //ver

  assert ps.Valid(input); //falla por 56 y 57, ver funciones con detalle
  
  
  assume false;
    if (ps.k == input.items.Length) { // hemos tratado todos los objetos
      if (ps.totalValue > bs.totalValue) {
        bs.totalValue := ps.totalValue;
        bs.totalWeight := ps.totalWeight;
        bs.itemsAssign := ps.itemsAssign;
        bs.k := ps.k;
      }
    }
    else { // la solución es completable --> llamada recursiva
      KnapsackVA(input, ps, bs);
    }
  
  ps.k := ps.k - 1; // desmarcar
  ps.totalWeight := ps.totalWeight - input.items[ps.k].weight; //desmarcar
  ps.totalValue := ps.totalValue - input.items[ps.k].value; // desmarcar

  assert ps.Valid(input);

  // RAMA NO COGEMOS EL OBJETO
  ps.itemsAssign[ps.k] := false;
  ps.k := ps.k + 1;
  if (ps.k == input.items.Length) { // hemos tratado todos los objetos
    if (ps.totalValue > bs.totalValue) {
      bs.totalValue := ps.totalValue;
      bs.totalWeight := ps.totalWeight;
      bs.itemsAssign := ps.itemsAssign;
      bs.k := ps.k;
    }
  }
  else { // la solución es completable --> llamada recursiva
    KnapsackVA(input, ps, bs);
  }
  ps.k := ps.k - 1;

}

