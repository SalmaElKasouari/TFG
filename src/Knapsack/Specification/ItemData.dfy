
datatype ItemData = ItemData(weight: real, value: real) {
  ghost predicate Valid() {
    weight > 0.0 && value > 0.0
  }
}
