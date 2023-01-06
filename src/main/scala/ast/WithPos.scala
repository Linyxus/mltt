package ast

trait WithPos {
  private var mySrcPos: SrcPos | Null = null
  def setPos(pos: SrcPos): this.type =
    mySrcPos = pos
    this
  def hasPos: Boolean = mySrcPos ne null
  def srcPos: SrcPos = mySrcPos.nn
}

