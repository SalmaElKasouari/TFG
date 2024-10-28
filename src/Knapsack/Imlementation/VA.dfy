
include "Solution.dfy"
include "Input.dfy"

/*
Método general que llama a la vuelta atrás. Se implementará de manera que el árbol de exploraciín sea un árbol 
binario, donde las etapas son los objetos que debemos tratar y las ramas representan la decisión de coger el objeto.

Tenemos ps (partial solution) y bs (best solution) de entrada y salida. El ps se irá rellenando con la vuelta atrás,
el bs guardará la mejor solución encontrada hasta el momento. Este último estará incializado a ceros, debido a que
tratamos con un problema de maximización.

*/

method KnapsackVA(input: Input, ps: Solution, bs: Solution) //poner o no (bs : Solution?)
  modifies ps, ps.itemsAssign, bs, bs.itemsAssign

  //Precondiciones
  requires input.Valid()
  requires ps.Partial(input)  
  //requires bs.Valid() no tiene sentido si bs puede venir como null (bs : Solution?)

  //Postcondiciones
  ensures ps.Partial(input)
  ensures bs.Valid(input)

  ensures ps.Model().itemsAssign == old(ps.Model().itemsAssign)
  ensures ps.Model().k == old(ps.k)
  ensures ps.Model().TotalValue(input.Model().items) == old(ps.Model().TotalValue(input.Model().items))
  ensures ps.Model().TotalWeight(input.Model().items) == old(ps.Model().TotalWeight(input.Model().items))

  
  ensures forall s : Solution | s.Model().OptimalExtension(ps.Model(), input.Model()) :: s.Model().TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items)
  ensures bs.Model().TotalWeight(input.Model().items) >= old(bs.Model().TotalWeight(input.Model().items))
  ensures bs.Model().TotalValue(input.Model().items) >= old(bs.Model().TotalValue(input.Model().items))
  ensures bs.Model().TotalValue(input.Model().items) == old(bs.Model().TotalValue(input.Model().items)) || bs.Model().TotalValue(input.Model().items) >= old(bs.Model().TotalValue(input.Model().items)) //o no se ha modificado, o se ha encontrado un nuevo valor mejor
  ensures bs.k == input.items.Length

  // Función de cota
  decreases ps.Bound()

{

  // Asertos para comprobar que sean valid las solutions
  assert ps.Partial(input); 
  assert ps.Model().TotalWeight(input.Model().items) == ps.totalWeight;
  assert ps.Model().TotalValue(input.Model().items) == ps.totalValue;
  // aquí bien, pero despues de modificar campos de ps falla valid


  // RAMA SI COGEMOS EL OBJETO
  ps.itemsAssign[ps.k] := true;
  ps.totalWeight := ps.totalWeight + input.items[ps.k].weight; // marcar
  ps.totalValue := ps.totalValue + input.items[ps.k].value; // marcar
  ps.k := ps.k + 1; // marcar

  assert input.Valid(); //ok, porque no se modifica
  assert ps.Model().TotalWeight(input.Model().items) == ps.totalWeight; //ver
  
  assert ps.Model().TotalValue(input.Model().items) == ps.totalValue; //ver

  assert ps.Valid(input); //falla por 59 y 61, ver funciones con detalle
  
  
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

