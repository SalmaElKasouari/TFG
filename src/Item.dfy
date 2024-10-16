class Item {
  const weight: real
  const value:  real

  constructor(w: real, v: real) {
    this.weight := w;
    this.value := v;
  }

  ghost predicate Valid () {
    this.weight > 0.0 && this.value > 0.0
  }



}