
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

method KnapsackVA(input: Input, ps: Solution, bs: Solution)
  decreases ps.Bound() // Función de cota
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
  else {
    // RAMA SI COGEMOS EL OBJETO
    if (ps.totalWeight + input.items[ps.k].weight <= input.maxWeight) {
      assert ps.totalWeight + input.items[ps.k].weight <= input.maxWeight;
      ghost var oldps := ps.Model();
      ghost var oldtotalWeight := ps.totalWeight;
      ghost var oldtotalValue := ps.totalValue;

      ps.itemsAssign[ps.k] := true;
      ps.totalWeight := ps.totalWeight + input.items[ps.k].weight;
      ps.totalValue := ps.totalValue + input.items[ps.k].value;
      ps.k := ps.k + 1;
      
      assert ps.Partial(input) by { 
        assert oldps.Partial(input.Model()); 
        assert oldtotalWeight == oldps.TotalWeight(input.Model().items);
        assert oldps.TotalWeight(input.Model().items) + input.items[ps.k - 1].weight <= input.maxWeight;
        calc {
          ps.Model().TotalWeight(input.Model().items);
          {SolutionData.AddTrueMaintainsSumConsistency(oldps, ps.Model(), input.Model());}
          oldps.TotalWeight(input.Model().items) + input.Model().items[ps.k - 1].weight;
          {input.inputDataItems(ps.k-1);}
          oldps.TotalWeight(input.Model().items) + input.items[ps.k - 1].weight;
           <= input.maxWeight;
        }
        calc {
          ps.totalWeight;
          oldtotalWeight + input.items[ps.k - 1].weight;
          oldps.TotalWeight(input.Model().items) + input.items[ps.k - 1].weight;
          { input.inputDataItems(ps.k-1);
          SolutionData.AddTrueMaintainsSumConsistency(oldps, ps.Model(), input.Model());
          }          
          ps.Model().TotalWeight(input.Model().items);
        }

        calc {
          ps.totalValue;
          oldtotalValue + input.items[ps.k - 1].value;
          oldps.TotalValue(input.Model().items) + input.items[ps.k - 1].value;
          {input.inputDataItems(ps.k-1);
          SolutionData.AddTrueMaintainsSumConsistency(oldps, ps.Model(), input.Model());
          }          
          ps.Model().TotalValue(input.Model().items);
        }
      }

      KnapsackVA(input, ps, bs);

      ps.k := ps.k - 1;
      ps.totalWeight := ps.totalWeight - input.items[ps.k].weight;
      ps.totalValue := ps.totalValue - input.items[ps.k].value;
    }
    
    ghost var oldps := ps.Model();
    // RAMA NO COGEMOS EL OBJETO
    ps.itemsAssign[ps.k] := false;
    ps.k := ps.k + 1;

    assert ps.Partial(input) by {
      SolutionData.AddFalsePreservesWeightValue(oldps, ps.Model(), input.Model());
      input.inputDataItems(ps.k-1);
    }

    KnapsackVA(input, ps, bs);

    ps.k := ps.k - 1;

  //La mejor solución deber ser una extension optima de ps
  assume bs.Model().OptimalExtension(ps.Model(), input.Model()) || bs.Model().equals(old(bs.Model()));

  //Cualquier extension optima de ps, su valor debe ser menor o igual que la mejor solucion (bs).
  assume forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model()) ::
            s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items);

  }

}

