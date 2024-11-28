include "../Specification/ItemData.dfy"

class Item {
  const weight: real
  const value:  real

  constructor(w: real, v: real)
    ensures this.weight == w
    ensures this.value == v
  {
    this.weight := w;
    this.value := v;
  }
  
  ghost function Model() : ItemData
    reads this
  {
    ItemData(this.weight, this.value)
  }

  ghost predicate Valid()
    reads this
  {
    this.weight > 0.0 && this.value > 0.0
  }



}