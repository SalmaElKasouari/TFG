include "InputData.dfy"
include "ItemData.dfy"
include "../../ContainersOps.dfy"
include "../../Math.dfy"

datatype SolutionData = SolutionData(itemsAssign: seq<bool>, k: nat) {

  static lemma {:induction} selectSeqFalses<T>(a :seq<T>, b : seq<bool>, startIdx : nat, endIdx : nat) // Ya no sería necesario porq hemos reescrito TotalWeight y TotalValue
    decreases endIdx - startIdx
    requires 0 <= startIdx <= endIdx <= |a|
    requires endIdx <= |b|
    requires forall i | 0 <= i < |b| :: !b[i]
    ensures selectSeq(a, b, startIdx, endIdx) == []
  {
    if startIdx == endIdx { //Base
      assert true;
    }
    else if b[startIdx] { // Esto nunca se alcanza porque todos son falsos (precondición)
      assert false;
    }
    else {
      selectSeqFalses(a, b, startIdx + 1, endIdx);
    }
  }

  lemma {:verify false} SumOfFalsesEqualsZero(input : InputData)
    requires k <= |itemsAssign|
    requires |itemsAssign| == |input.items|
    requires forall i | 0 <= i < |itemsAssign| :: !itemsAssign[i]
    ensures && TotalWeight(input.items) == 0.0
            && TotalValue(input.items) == 0.0
  {
    /* Si ningun objeto ha sido seleccionado (todos asignados a false --> array objetos seleccionado es vacio), 
    la suma total de los pesos/valores de los objetos escogidos (ninguno) es 0 */

    if k == 0 {
      assert TotalWeight(input.items) == 0.0 && TotalValue(input.items) == 0.0;
    }
    else if itemsAssign[k-1] {
      assert false;
    }
    else { // !itemsAssign[k-1]
      // Inducción: el peso/valor total hasta k es igual al peso/valor total hasta k-1 (se suma 0 por ser false)
      assert TotalWeight(input.items) == 0.0 by {
        assert SolutionData(itemsAssign, k).TotalWeight(input.items) == SolutionData(itemsAssign, k - 1).TotalWeight(input.items) + (if itemsAssign[k-1] then input.items[k-1].weight else 0.0);
        assert !itemsAssign[k-1];
        assert SolutionData(itemsAssign, k).TotalWeight(input.items) == SolutionData(itemsAssign, k - 1).TotalWeight(input.items);
      }

      assert TotalValue(input.items) == 0.0 by {
        assert SolutionData(itemsAssign, k).TotalValue(input.items) == SolutionData(itemsAssign, k - 1).TotalValue(input.items) + (if itemsAssign[k-1] then input.items[k-1].weight else 0.0);
        assert !itemsAssign[k-1];
        assert SolutionData(itemsAssign, k).TotalValue(input.items) == SolutionData(itemsAssign, k - 1).TotalValue(input.items);
      }
    }
  }

  /*
    Este lema establece que al añadir en s1 un elemento asignado a true (en itemsAssign), la suma de los pesos
    y los valores del conjunto total (s2) se actualiza de manera consistente al incluir el peso y el valor 
    del nuevo elemento.
  */
  lemma AddTrueMaintainsSumConsistency(s1 : SolutionData, s2 : SolutionData, input : InputData) //s1 viejo, s2 nuevo
    requires 0 < s1.k == s2.k <= |input.items| //array no vacío
    requires 0 < s1.k == s2.k <= |input.items| - 1 //array no vacío
    requires 0 < k <= |itemsAssign|
    requires s2.k == s1.k + 1
    requires s1.itemsAssign[..s1.k - 1] + [true] == s2.itemsAssign
    ensures s1.TotalWeight(input.items) + input.items[s1.k].weight ==
            s2.TotalWeight(input.items)
    ensures s1.TotalValue(input.items) + input.items[s1.k].value ==
            s2.TotalValue(input.items)
  {
    assert input.items == input.items[..|input.items| - 1] + [input.items[|input.items| - 1]];
    assert s1.TotalWeight(input.items) + input.items[s1.k].weight == s2.TotalWeight(input.items) by {
      calc {
        s2.TotalWeight(input.items);
        s1.TotalWeight(input.items[..|input.items| - 1] + [input.items[|input.items| - 1]]);
        s1.TotalWeight(input.items) + input.items[s1.k].weight;
      }
    }

    // Lo intuye directamente
    assert s1.TotalWeight(input.items) + input.items[s1.k].weight == s2.TotalWeight(input.items);
    assert s1.TotalValue(input.items) + input.items[s1.k].value == s2.TotalValue(input.items);
  }

  /*
    Este lema establece que al añadir un elemento false en itemsAssign, la suma total de los pesos 
    y los valores sigue siendo la misma y no se ve alterada (ya que no sumaría el peso del objeto
    como se ve en la definición de Totalweight y TotalValue) 
  */
  lemma AddFalsePreservesWeight(s1 : SolutionData, s2 : SolutionData, input : InputData) //s1 viejo, s2 nuevo
    requires 0 < s1.k == s2.k <= |input.items| //array no vacío
    requires 0 < s1.k == s2.k <= |input.items| - 1 //array no vacío
    requires 0 < k <= |itemsAssign|
    requires s2.k == s1.k + 1
    requires s1.itemsAssign[..s1.k - 1] + [false] == s2.itemsAssign
    ensures s1.TotalWeight(input.items) == s2.TotalWeight(input.items)
    ensures s1.TotalValue(input.items) == s2.TotalValue(input.items)
  {
    assert s1.TotalWeight(input.items) == s2.TotalWeight(input.items);
    assert s1.TotalValue(input.items) == s2.TotalValue(input.items);

    //assert input.items == input.items[..|input.items| - 1] + [input.items[|input.items| - 1]];
    // assert s1.TotalWeight(input.items) + input.items[s1.k].weight == s2.TotalWeight(input.items) by {
    //   assert s2.TotalWeight(input.items) == s1.TotalWeight(input.items[..|input.items| - 1] + [input.items[|input.items| - 1]]);
    //   assert s1.TotalWeight(input.items[..|input.items| - 1] + [input.items[|input.items| - 1]]) == s1.TotalWeight(input.items) + input.items[s1.k].weight;
    // }
  }

  /*
    Este lema establece que el peso y valor totales de una SolutionData es igual al peso y valor totales 
    del modelo de nuestra solución objeto (Solution).    
  */
  lemma EqualTotalValueAndTotalWeight(s : SolutionData, input : InputData)
    requires |input.items| == |this.itemsAssign| == |s.itemsAssign|
    requires this.k <= |this.itemsAssign|
    requires s.k <= |s.itemsAssign|
    requires this.equals(s)
    ensures this.TotalValue(input.items) == s.TotalValue(input.items)
    ensures this.TotalWeight(input.items) == s.TotalWeight(input.items)

  lemma ValidSumEnsuresPartial(input : InputData) //(?)
    requires 0 <= k < |input.items|
    requires 0 <= k < |itemsAssign|
    requires this.TotalWeight(input.items) <= input.maxWeight
    ensures this.Partial(input)

  ghost function TotalWeight(items: seq<ItemData>): real
    decreases k
    requires k <= |items|
    requires k <= |itemsAssign|
  {
    if k == 0 then
      0.0
    else if itemsAssign[k-1] then
      SolutionData(itemsAssign, k - 1).TotalWeight(items) + items[k-1].weight
    else
      SolutionData(itemsAssign, k - 1).TotalWeight(items)
  }

  ghost function TotalValue(items: seq<ItemData>): real
    decreases k
    requires k <= |items|
    requires k <= |itemsAssign|
  {
    if k == 0 then
      0.0
    else if itemsAssign[k-1] then
      SolutionData(itemsAssign, k - 1).TotalValue(items) + items[k-1].weight
    else
      SolutionData(itemsAssign, k - 1).TotalValue(items)
  }

  ghost predicate Partial (input: InputData){
    && 0 <= k <= |itemsAssign|
    && |itemsAssign| == |input.items|
    && this.TotalWeight(input.items) <= input.maxWeight
  }

  ghost predicate Valid(input: InputData){
    && k == |itemsAssign|
    && Partial(input)
  }

  ghost predicate Optimal(input: InputData)
    requires this.Valid(input)
    requires input.Valid()
  {
    forall otherSolution: SolutionData | otherSolution.Valid(input) :: otherSolution.TotalValue(input.items) <= TotalValue(input.items)
  }

  ghost predicate Extends(ps : SolutionData) // ps es prefijo de ps' (el que llama a la función), (ps y ps' iguales hasta k)
    requires |this.itemsAssign| == |ps.itemsAssign|
    requires this.k <= |this.itemsAssign|
    requires ps.k <= this.k
  {
    forall i | 0 <= i < ps.k :: this.itemsAssign[i] == ps.itemsAssign[i]
  }

  ghost predicate OptimalExtension(ps : SolutionData, input : InputData)
    requires input.Valid()
  {
    && this.Valid(input)
    && ps.Partial(input)
    && this.Extends(ps)
    && forall s : SolutionData | s.Valid(input) && s.Extends(ps) :: s.TotalValue(input.items) <= this.TotalValue(input.items)
  }

  ghost predicate equals(s : SolutionData)
    requires |this.itemsAssign| == |s.itemsAssign|
    requires this.k <= |this.itemsAssign|
    requires s.k <= |s.itemsAssign|
  {
    && this.k == s.k
    && forall i | 0 <= i < this.k :: this.itemsAssign[i] == s.itemsAssign[i]
  }

}