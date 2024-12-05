
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
      bs.copyModel(ps, input);

      forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model())
      ensures s.TotalValue(input.Model().items) <= bs.Model().TotalValue(input.Model().items) {
        assert s.equals(ps.Model());
        calc {
          s.TotalValue(input.Model().items); { s.EqualTotalValueAndTotalWeight(ps.Model(), input.Model());}
          ps.Model().TotalValue(input.Model().items);
          {assume false;}
        }
      }
      assume false;
    }
    assume false;

    assert ps.totalValue <= bs.totalValue;
    forall s : SolutionData | s.Valid(input.Model()) && s.Extends(ps.Model())
      ensures 
      s.equals(ps.Model()) 
      //&& s.TotalWeight(input.Model().items) == ps.totalWeight 
    {
    }

  }
  else {
    assume false;
    // RAMA SI COGEMOS EL OBJETO
    if (ps.totalWeight + input.items[ps.k].weight <= input.maxWeight) {
      assert ps.totalWeight + input.items[ps.k].weight <= input.maxWeight;

      ps.itemsAssign[ps.k] := true;
      ps.totalWeight := ps.totalWeight + input.items[ps.k].weight;
      ps.totalValue := ps.totalValue + input.items[ps.k].value;
      ps.k := ps.k + 1;
      assert ps.Partial(input) by {
        assume false;
        assert 0 <= ps.k <= ps.itemsAssign.Length;
        assert ps.Model().Partial(input.Model()); //ncesitará saber que lo que hemos sumado es justo lo que esta en el if y por tanto es valido
        
        //lemma para totalweight        
        assert ps.Model().TotalWeight(input.Model().items) == ps.totalWeight by {
          ps.Model().RemoveComponentMaintainsWeightSum(input.Model().items);
        }
        //lemma para totalvalue
        assert ps.Model().TotalValue(input.Model().items) == ps.totalValue;
      }

      KnapsackVA(input, ps, bs);

      ps.k := ps.k - 1;
      ps.totalWeight := ps.totalWeight - input.items[ps.k].weight;
      ps.totalValue := ps.totalValue - input.items[ps.k].value;
    }

    // RAMA NO COGEMOS EL OBJETO
    ps.itemsAssign[ps.k] := false;
    ps.k := ps.k + 1;

    assert ps.Partial(input) by {
      //assume false;
      assert 0 <= ps.k <= ps.itemsAssign.Length;
      assert ps.Model().Partial(input.Model());
      //lemma de a una suma total le añadimos un obieto no selecionado (false) igue siendo la misma uma porq suma 0
      assert ps.Model().TotalWeight(input.Model().items) == ps.totalWeight;
      //lemma
      assert ps.Model().TotalValue(input.Model().items) == ps.totalValue;
    }

    KnapsackVA(input, ps, bs);

    ps.k := ps.k - 1;

    
    assert ps.Partial(input) by { //demo con igualdad campos (old y actual) con ensures
      assert 0 <= ps.k <= ps.itemsAssign.Length;
      assert ps.Model().Partial(input.Model());
      assert ps.Model().TotalWeight(input.Model().items) == ps.totalWeight;
      assert ps.Model().TotalValue(input.Model().items) == ps.totalValue;
    }
    //assume bs.Model().OptimalExtension(ps.Model(), input.Model()) || bs.Model().equals(old(bs.Model()));

  }

}

