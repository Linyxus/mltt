package ast

case class SrcPos(from: Int, until: Int):
  def to (other: SrcPos): SrcPos =
    def min(a: Int, b: Int): Int = if a >= b then b else a
    def max(a: Int, b: Int): Int = if a >= b then a else b
    SrcPos(min(from, other.from), max(until, other.until))

