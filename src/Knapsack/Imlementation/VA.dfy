
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

  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)

  requires bs.itemsAssign != ps.itemsAssign
  requires bs != ps

  ensures ps.Partial(input) //dentro ya comprueba ps.itemsAssign.Length == input.items.Length
  ensures ps.Model().equals(old(ps.Model())) // las ps actual y antigua deben ser iguales hasta la k

  //La mejor solución debe ser válida
  ensures bs.Valid(input) //dentro ya comprueba bs.itemsAssign.Length == input.items.Length

  //La mejor solución deber ser una extension optima de ps
  ensures bs.Model().OptimalExtension(ps.Model(), input.Model()) || bs.Model().equals(old(bs.Model()))

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  ensures forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) :: 
  s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items) // Esta postcond Dafny no la puede verificar porque no hay cuerpo del metodo supongo

  // Si bs cambia, su nuevo valor total debe ser mayor o igual al valor anterior
  ensures bs.Model().TotalValue(input.Model().items) >= old(bs.Model().TotalValue(input.Model().items))

{

  if (ps.k == input.items.Length) { // hemos tratado todos los objetos
  forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) :: s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items);
    if (ps.totalValue > bs.totalValue) {
      bs.totalValue := ps.totalValue;
      bs.totalWeight := ps.totalWeight;
      bs.itemsAssign := ps.itemsAssign; //copiar elemento a elemento (metodo aparte)
      bs.k := ps.k;
    }
  }
  else {
    assume false;
    // RAMA SI COGEMOS EL OBJETO
    var valid := ps.totalWeight + input.items[ps.k].weight <= input.maxWeight;
    if (valid) { //si uso ps.Partial() no deja asignar valores a los campos de ps
      ps.itemsAssign[ps.k] := true;
      ps.totalWeight := ps.totalWeight + input.items[ps.k].weight;
      ps.totalValue := ps.totalValue + input.items[ps.k].value;
      ps.k := ps.k + 1;

      KnapsackVA(input, ps, bs);

      ps.k := ps.k - 1;
      ps.totalWeight := ps.totalWeight - input.items[ps.k].weight;
      ps.totalValue := ps.totalValue - input.items[ps.k].value;
    }



    // // RAMA NO COGEMOS EL OBJETO
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

}

