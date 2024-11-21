
include "Solution.dfy"
include "Input.dfy"
include "../../Ord.dfy"

/*
Método general que llama a la vuelta atrás. Se implementará de manera que el árbol de exploraciín sea un árbol 
binario, donde las etapas son los objetos que debemos tratar y las ramas representan la decisión de coger el objeto.

Tenemos ps (partial solution) y bs (best solution) de entrada y salida. El ps se irá rellenando con la vuelta atrás,
el bs guardará la mejor solución encontrada hasta el momento. Este último estará incializado a ceros, debido a que
tratamos con un problema de maximización.

*/


method KnapsackVA(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound() // Función de cota
  modifies ps, ps.itemsAssign, bs, bs.itemsAssign

  //Precondiciones
  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)
  
  //Postcondiciones
  ensures ps.Partial(input) //dentro ya comprueba ps.itemsAssign.Length == input.items.Length
  ensures ps.Model().equals(old(ps.Model())) // las ps actual y antigua deben ser iguales hasta la k
  
  //La mejor solución debe ser válida
  ensures bs.Valid(input) //dentro ya comprueba bs.itemsAssign.Length == input.items.Length
  
  //La mejor solución deber ser una extension optima de ps 
  ensures bs.OptimalExtension(ps, input) || bs.Model().equals(old(bs.Model()))

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  
  ensures forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) :: s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items) // Esta postcond Dafny no la puede verificar porque no hay cuerpo del metodo supongo

  // Si bs cambia, su nuevo valor total debe ser mayor o igual al valor anterior
  ensures bs.Model().TotalValue(input.Model().items) >= old(bs.Model().TotalValue(input.Model().items))

  //Se deduce que bs es el maximo de ( ,)

// {

//   // // Asertos para comprobar que sean valid las solutions
//   // assert ps.Partial(input); 
//   // assert ps.Model().TotalWeight(input.Model().items) == ps.totalWeight;
//   // assert ps.Model().TotalValue(input.Model().items) == ps.totalValue;
//   // // aquí bien, pero despues de modificar campos de ps falla valid


//   // // RAMA SI COGEMOS EL OBJETO
//   // ps.itemsAssign[ps.k] := true;
//   // ps.totalWeight := ps.totalWeight + input.items[ps.k].weight; // marcar
//   // ps.totalValue := ps.totalValue + input.items[ps.k].value; // marcar
//   // ps.k := ps.k + 1; // marcar

//   // assert input.Valid(); //ok, porque no se modifica
//   // assert ps.Model().TotalWeight(input.Model().items) == ps.totalWeight; //ver
  
//   // assert ps.Model().TotalValue(input.Model().items) == ps.totalValue; //ver

//   // assert ps.Valid(input); //falla por 59 y 61, ver funciones con detalle
  
  
//   // assume false;
//   //   if (ps.k == input.items.Length) { // hemos tratado todos los objetos
//   //     if (ps.totalValue > bs.totalValue) {
//   //       bs.totalValue := ps.totalValue;
//   //       bs.totalWeight := ps.totalWeight;
//   //       bs.itemsAssign := ps.itemsAssign;
//   //       bs.k := ps.k;
//   //     }
//   //   }
//   //   else { // la solución es completable --> llamada recursiva
//   //     KnapsackVA(input, ps, bs);
//   //   }
  
//   // ps.k := ps.k - 1; // desmarcar
//   // ps.totalWeight := ps.totalWeight - input.items[ps.k].weight; //desmarcar
//   // ps.totalValue := ps.totalValue - input.items[ps.k].value; // desmarcar

//   // assert ps.Valid(input);

//   // // RAMA NO COGEMOS EL OBJETO
//   // ps.itemsAssign[ps.k] := false;
//   // ps.k := ps.k + 1;
//   // if (ps.k == input.items.Length) { // hemos tratado todos los objetos
//   //   if (ps.totalValue > bs.totalValue) {
//   //     bs.totalValue := ps.totalValue;
//   //     bs.totalWeight := ps.totalWeight;
//   //     bs.itemsAssign := ps.itemsAssign;
//   //     bs.k := ps.k;
//   //   }
//   // }
//   // else { // la solución es completable --> llamada recursiva
//   //   KnapsackVA(input, ps, bs);
//   // }
//   // ps.k := ps.k - 1;

// }

