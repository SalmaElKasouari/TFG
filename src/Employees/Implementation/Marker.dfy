
include "Solution.dfy"

class Marker {
  var marker: array<bool>

  constructor(marker': array<bool>)
    ensures this.marker == marker'
  {
    this.marker := marker';
  }
  
  ghost predicate Valid(s : Solution)
  {
    && s.employeesAssign.Length == marker.Length
    && forall i | 0 <= i < s.employeesAssign.Length :: marker[i] == (i in s.Model().employeesAssign[0..s.k])
  }
}