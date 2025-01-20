
include "Solution.dfy"
include "../Specification/SolutionData.dfy"
include "Input.dfy"
include "../../Ord.dfy"

/*
Método general que llama a la vuelta atrás. Se implementará de manera que el árbol de exploraciín sea un árbol 
binario, donde las etapas son los objetos que debemos tratar y las ramas representan la decisión de coger el objeto.

Tenemos ps (partial solution) y bs (best solution) de entrada y salida. El ps se irá rellenando con la vuelta atrás,
el bs guardará la mejor solución encontrada hasta el momento. Este último estará incializado a ceros, debido a que
tratamos con un problema de maximización.

*/

lemma PartialConsistency(ps: Solution, oldps: SolutionData, input: Input, oldtotalWeight: real, oldtotalValue: real) //añadidos todos los requires necesarios, falla la suma pero en VA va bien
  requires 1 <= ps.k <= ps.itemsAssign.Length == input.items.Length
  requires 0 <= oldps.k <= |oldps.itemsAssign|
  requires ps.k == oldps.k + 1
  requires ps.itemsAssign.Length == |oldps.itemsAssign| == input.items.Length
  requires oldps.itemsAssign[..oldps.k] + [true] == ps.itemsAssign[..ps.k]
  requires oldps.Partial(input.Model())
  requires oldtotalWeight == oldps.TotalWeight(input.Model().items)
  requires oldtotalValue == oldps.TotalValue(input.Model().items)
  requires oldps.TotalWeight(input.Model().items) + input.items[ps.k - 1].weight <= input.maxWeight
  requires oldtotalWeight == ps.totalWeight - input.items[oldps.k].weight
  requires oldtotalValue == ps.totalValue - input.items[oldps.k].value
  ensures ps.Partial(input)
{
  assert oldps.Partial(input.Model());
  assert oldtotalWeight == oldps.TotalWeight(input.Model().items);
  assert oldps.TotalWeight(input.Model().items) + input.items[ps.k - 1].weight <= input.maxWeight;

  calc {
     ps.Model().TotalWeight(input.Model().items);
    { SolutionData.AddTrueMaintainsSumConsistency(oldps, ps.Model(), input.Model()); }
     oldps.TotalWeight(input.Model().items) + input.Model().items[ps.k - 1].weight;
    { input.InputDataItems(ps.k - 1); }
     oldps.TotalWeight(input.Model().items) + input.items[ps.k - 1].weight;
  <= input.maxWeight;
  }

  calc {
    ps.totalWeight;
    oldtotalWeight + input.items[ps.k - 1].weight;
    oldps.TotalWeight(input.Model().items) + input.items[ps.k - 1].weight;
    { input.InputDataItems(ps.k - 1);
      SolutionData.AddTrueMaintainsSumConsistency(oldps, ps.Model(), input.Model());
    }
    ps.Model().TotalWeight(input.Model().items);
  }

  calc {
    ps.totalValue;
    oldtotalValue + input.items[ps.k - 1].value;
    oldps.TotalValue(input.Model().items) + input.items[ps.k - 1].value;
    { input.InputDataItems(ps.k - 1);
      SolutionData.AddTrueMaintainsSumConsistency(oldps, ps.Model(), input.Model());
    }
    ps.Model().TotalValue(input.Model().items);
  }

  assert ps.Partial(input);
}

method KnapsackVABaseCase(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound() // Función de cota
  modifies ps`totalValue, ps`totalWeight, ps`k, ps.itemsAssign
  modifies bs`totalValue, bs`totalWeight, bs`k, bs.itemsAssign

  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires bs.itemsAssign != ps.itemsAssign
  requires bs != ps

  requires ps.k == input.items.Length

  ensures ps.Partial(input) //dentro ya comprueba ps.itemsAssign.Length == input.items.Length
  ensures ps.Model().equals(old(ps.Model())) // las ps actual y antigua deben ser iguales hasta la k
  ensures ps.k == old (ps.k)
  ensures ps.totalValue == old(ps.totalValue)
  ensures ps.totalWeight == old(ps.totalWeight)

  //La mejor solución debe ser válida
  ensures bs.Valid(input)

  //La mejor solución deber ser una extension optima de ps
  ensures bs.Model().OptimalExtension(ps.Model(), input.Model()) || bs.Model().equals(old(bs.Model()))

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  ensures forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
            s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items)

  // Si bs cambia, su nuevo valor total debe ser mayor o igual al valor anterior
  ensures bs.Model().TotalValue(input.Model().items) >= old(bs.Model().TotalValue(input.Model().items))
{
  if (ps.totalValue > bs.totalValue) {
    bs.Copy(ps);
    forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model())
      ensures s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items) {
      assert s.equals(ps.Model());
      calc {
        s.TotalValue(input.Model().items);
        {s.EqualTotalValueAndTotalWeight(ps.Model(), input.Model());}
        ps.Model().TotalValue(input.Model().items);
        {bs.copyModel(ps, input);}
        bs.Model().TotalValue(input.Model().items);
      }
    }
  }
  else { // ps.totalValue <= bs.totalValue
    forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model())
      ensures s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items) {
      assert s.equals(ps.Model());
      s.EqualTotalValueAndTotalWeight(ps.Model(), input.Model());
      assert s.TotalValue(input.Model().items) == ps.Model().TotalValue(input.Model().items);
    }
  }
}

method KnapsackVAFalseBranch(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound(),0 // Función de cota
  modifies ps`totalValue, ps`totalWeight, ps`k, ps.itemsAssign
  modifies bs`totalValue, bs`totalWeight, bs`k, bs.itemsAssign

  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires bs.itemsAssign != ps.itemsAssign
  requires bs != ps

  requires ps.k < input.items.Length

  ensures ps.Partial(input) //dentro ya comprueba ps.itemsAssign.Length == input.items.Length
  ensures ps.Model().equals(old(ps.Model())) // las ps actual y antigua deben ser iguales hasta la k
  ensures ps.k == old (ps.k)
  ensures ps.totalValue == old(ps.totalValue)
  ensures ps.totalWeight == old(ps.totalWeight)

  //La mejor solución debe ser válida
  ensures bs.Valid(input)

  //La mejor solución deber ser una extension optima de ps
  ensures bs.Model().OptimalExtension( SolutionData(ps.Model().itemsAssign[ps.k:=false],ps.k+1), input.Model())
          || bs.Model().equals(old(bs.Model()))

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  ensures forall s : SolutionData | s.Valid(input.Model()) && s.Extends(SolutionData(ps.Model().itemsAssign[ps.k:=false],ps.k+1)) ::
            s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items)

  // Si bs cambia, su nuevo valor total debe ser mayor o igual al valor anterior
  ensures bs.Model().TotalValue(input.Model().items) >= old(bs.Model().TotalValue(input.Model().items))

{
  ghost var oldps := ps.Model();
  ps.itemsAssign[ps.k] := false;
  ps.k := ps.k + 1;

  assert ps.Partial(input) by {
    SolutionData.AddFalsePreservesWeightValue(oldps, ps.Model(), input.Model());
    input.InputDataItems(ps.k-1);
  }

  KnapsackVA(input, ps, bs);

  label L:

  ps.k := ps.k - 1;

  assert SolutionData(ps.Model().itemsAssign[ps.k := false], ps.k + 1) == old@L(ps.Model());

  //La mejor solución deber ser una extension optima de ps
  assert bs.Model().OptimalExtension(SolutionData(ps.Model().itemsAssign[ps.k:=false], ps.k+1), input.Model())
         || bs.Model().equals(old(bs.Model()));

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  assert forall s : SolutionData | s.Valid(input.Model()) && s.Extends(SolutionData(ps.Model().itemsAssign[ps.k:=false],ps.k+1)) ::
      s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items);


}

method KnapsackVATrueBranch(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound(),0 // Función de cota
  modifies ps`totalValue, ps`totalWeight, ps`k, ps.itemsAssign
  modifies bs`totalValue, bs`totalWeight, bs`k, bs.itemsAssign

  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires bs.itemsAssign != ps.itemsAssign
  requires bs != ps

  requires ps.k < input.items.Length
  requires ps.totalWeight + input.items[ps.k].weight <= input.maxWeight

  ensures ps.Partial(input) //dentro ya comprueba ps.itemsAssign.Length == input.items.Length
  ensures ps.Model().equals(old(ps.Model())) // las ps actual y antigua deben ser iguales hasta la k
  ensures ps.k == old (ps.k)
  ensures ps.totalValue == old(ps.totalValue)
  ensures ps.totalWeight == old(ps.totalWeight)

  //La mejor solución debe ser válida
  ensures bs.Valid(input)

  ensures bs.Model().OptimalExtension( SolutionData(ps.Model().itemsAssign[ps.k:=true],ps.k+1), input.Model())
          || bs.Model().equals(old(bs.Model()))

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  ensures forall s : SolutionData | s.Valid(input.Model()) && s.Extends(SolutionData(ps.Model().itemsAssign[ps.k:=true],ps.k+1)) ::
            s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items)

  // Si bs cambia, su nuevo valor total debe ser mayor o igual al valor anterior
  ensures bs.Model().TotalValue(input.Model().items) >= old(bs.Model().TotalValue(input.Model().items))

{
  assert ps.totalWeight + input.items[ps.k].weight <= input.maxWeight;
  ghost var oldps := ps.Model();
  ghost var oldtotalWeight := ps.totalWeight;
  ghost var oldtotalValue := ps.totalValue;

  ps.itemsAssign[ps.k] := true;
  ps.totalWeight := ps.totalWeight + input.items[ps.k].weight;
  ps.totalValue := ps.totalValue + input.items[ps.k].value;
  ps.k := ps.k + 1;

  PartialConsistency(ps, oldps, input, oldtotalWeight, oldtotalValue); //añadidos todos los requires necesarios, falla la suma pero en VA va bien

  KnapsackVA(input, ps, bs);

  label L: 

  ps.k := ps.k - 1;
  ps.totalWeight := ps.totalWeight - input.items[ps.k].weight;
  ps.totalValue := ps.totalValue - input.items[ps.k].value;

  assert SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k + 1) == old@L(ps.Model());

  //La mejor solución deber ser una extension optima de ps
  assert bs.Model().OptimalExtension( SolutionData(ps.Model().itemsAssign[ps.k:=true],ps.k+1), input.Model())
         || bs.Model().equals(old(bs.Model()));

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  assert forall s : SolutionData | s.Valid(input.Model()) && s.Extends(SolutionData(ps.Model().itemsAssign[ps.k:=true],ps.k+1)) ::
      s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items);
}

method KnapsackVA(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound(),1 // Función de cota
  modifies ps`totalValue, ps`totalWeight, ps`k, ps.itemsAssign
  modifies bs`totalValue, bs`totalWeight, bs`k, bs.itemsAssign

  requires input.Valid()
  requires ps.Partial(input)
  requires bs.Valid(input)
  requires bs.itemsAssign != ps.itemsAssign
  requires bs != ps

  ensures ps.Partial(input) //dentro ya comprueba ps.itemsAssign.Length == input.items.Length
  ensures ps.Model().equals(old(ps.Model())) // las ps actual y antigua deben ser iguales hasta la k
  ensures ps.k == old (ps.k)
  ensures ps.totalValue == old(ps.totalValue)
  ensures ps.totalWeight == old(ps.totalWeight)

  //La mejor solución debe ser válida
  ensures bs.Valid(input)

  //La mejor solución deber ser una extension optima de ps
  ensures bs.Model().OptimalExtension(ps.Model(), input.Model()) || bs.Model().equals(old(bs.Model()))

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  ensures forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
            s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items)

  // Si bs cambia, su nuevo valor total debe ser mayor o igual al valor anterior
  ensures bs.Model().TotalValue(input.Model().items) >= old(bs.Model().TotalValue(input.Model().items))

{

  if (ps.k == input.items.Length) { // hemos tratado todos los objetos
    KnapsackVABaseCase(input, ps, bs);
  }
  else {
    if (ps.totalWeight + input.items[ps.k].weight <= input.maxWeight) {
      KnapsackVATrueBranch(input, ps, bs);
    }

    label L:

    ghost var oldbs := bs.Model();
    assert ps.Model().equals(old(ps.Model()));
    assert oldbs.OptimalExtension( SolutionData(ps.Model().itemsAssign[ps.k:=true],ps.k+1), input.Model())
           || oldbs.equals(old(bs.Model()));


    KnapsackVAFalseBranch(input, ps, bs);

    assert bs.Model().OptimalExtension( SolutionData(ps.Model().itemsAssign[ps.k:=false], ps.k+1), input.Model())
           || bs.Model().equals(oldbs);
    assert ps.Model().equals(old(ps.Model()));

    if bs.Model().OptimalExtension(SolutionData(ps.Model().itemsAssign[ps.k := false], ps.k+1), input.Model()) {

    }
    else if oldbs.equals(old(bs.Model())) { //bs.Model().equals(oldbs)

    }
    else {
      assert bs.Model().equals(oldbs);

      assert oldbs.OptimalExtension(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k+1), input.Model());
    }

    assume  forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
        s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items);

  }

}