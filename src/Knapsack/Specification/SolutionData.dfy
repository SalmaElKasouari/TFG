include "InputData.dfy"
include "ItemData.dfy"
include "../../ContainersOps.dfy"
include "../../Math.dfy"
include "../Implementation/Input.dfy"
include "../Implementation/Solution.dfy"

datatype SolutionData = SolutionData(itemsAssign: seq<bool>, k: nat) {

  lemma SumOfFalsesEqualsZero(input : InputData)
    decreases k
    requires k <= |itemsAssign|
    requires |itemsAssign| == |input.items|
    requires forall i | 0 <= i < |itemsAssign| :: !itemsAssign[i]
    ensures && TotalWeight(input.items) == 0.0
            && TotalValue(input.items) == 0.0
  {
    /* Si ningun objeto ha sido seleccionado (todos asignados a false --> array objetos seleccionado es vacio), 
    la suma total de los pesos/valores de los objetos escogidos (ninguno) es 0 */
  }

  /*
    Este lema establece que al añadir en s1 un elemento asignado a true (en itemsAssign), la suma de los pesos
    y los valores del conjunto total (s2) se actualiza de manera consistente al incluir el peso y el valor 
    del nuevo elemento.
  */
  static lemma AddTrueMaintainsSumConsistency(s1 : SolutionData, s2 : SolutionData, input : InputData) //s1 viejo, s2 nuevo
    decreases s1.k
    requires 0 <= s1.k <= |s1.itemsAssign|
    requires 0 < s2.k <= |s2.itemsAssign|
    requires |s2.itemsAssign| == |s1.itemsAssign| == |input.items|
    requires s2.k == s1.k + 1
    requires s1.itemsAssign[..s1.k] + [true] == s2.itemsAssign[..s2.k]
    ensures s1.TotalWeight(input.items) + input.items[s1.k].weight ==
            s2.TotalWeight(input.items)
    ensures s1.TotalValue(input.items) + input.items[s1.k].value ==
            s2.TotalValue(input.items)
  {
    s1.EqualTotalValueAndTotalWeight(SolutionData(s2.itemsAssign, s2.k-1), input);
  }

  /*
    Este lema establece que al añadir un elemento false en itemsAssign, la suma total de los pesos 
    y los valores sigue siendo la misma y no se ve alterada (ya que no sumaría el peso del objeto
    como se ve en la definición de Totalweight y TotalValue) 
  */
  static lemma AddFalsePreservesWeightValue(s1 : SolutionData, s2 : SolutionData, input : InputData) //s1 viejo, s2 nuevo
    decreases s1.k
    requires 0 <= s1.k <= |s1.itemsAssign|
    requires 0 < s2.k <= |s2.itemsAssign|
    requires |s2.itemsAssign| == |s1.itemsAssign| == |input.items|
    requires s2.k == s1.k + 1
    requires s1.itemsAssign[..s1.k] + [false] == s2.itemsAssign[..s2.k]
    ensures s1.TotalWeight(input.items) == s2.TotalWeight(input.items)
    ensures s1.TotalValue(input.items) == s2.TotalValue(input.items)
  {
    s1.EqualTotalValueAndTotalWeight(SolutionData(s2.itemsAssign, s2.k-1), input);
  }

  /*
    Este lema establece que el peso y valor totales de una SolutionData es igual al peso y valor totales 
    del modelo de nuestra solución objeto (Solution).    
  */
  lemma {:induction this,s} EqualTotalValueAndTotalWeight(s : SolutionData, input : InputData)
    decreases k
    requires |input.items| == |this.itemsAssign| == |s.itemsAssign|
    requires this.k <= |this.itemsAssign|
    requires s.k <= |s.itemsAssign|
    requires this.equals(s)
    ensures this.TotalValue(input.items) == s.TotalValue(input.items)
    ensures this.TotalWeight(input.items) == s.TotalWeight(input.items)
  {
    if k == 0 {

    }
    else if itemsAssign[k-1] {
      SolutionData(itemsAssign, k - 1).EqualTotalValueAndTotalWeight(SolutionData(s.itemsAssign, s.k-1), input);
    }
    else {
      SolutionData(itemsAssign, k - 1).EqualTotalValueAndTotalWeight(SolutionData(s.itemsAssign, s.k-1), input);
    }
  }

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
      SolutionData(itemsAssign, k - 1).TotalValue(items) + items[k-1].value
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

  /*
  Si una bs es una extesnion optima de ps + true o de ps + false, entonces bs es una extension optima de ps
  */
  lemma OptimalExtensionOfTrueOrFalseBranch(input: Input, ps: Solution, bs: Solution)
    requires input.Valid()
    requires ps.Partial(input)
    requires bs.Valid(input)
    requires ps.k < input.items.Length
    requires
      || bs.Model().OptimalExtension(SolutionData(ps.Model().itemsAssign[ps.k := true], ps.k + 1), input.Model())
      || bs.Model().OptimalExtension(SolutionData(ps.Model().itemsAssign[ps.k := false], ps.k + 1), input.Model())

    ensures bs.Model().OptimalExtension(ps.Model(), input.Model())
  {
    assume false;
    if (bs.Model().OptimalExtension(SolutionData(ps.Model().itemsAssign[ps.k := false], ps.k + 1), input.Model())) {

    }
    else {

    }
  }

  lemma EqualsOptimalextension(ps1 : SolutionData, ps2: SolutionData, input : InputData)
    requires this.Valid(input)
    requires input.Valid()
    requires ps1.Partial(input)
    requires ps2.Partial(input)
    requires this.OptimalExtension(ps1, input)
    ensures this.OptimalExtension(ps2, input)
  


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