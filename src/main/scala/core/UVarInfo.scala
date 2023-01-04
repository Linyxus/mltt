package core

import ast.TypedExprs._
import Context.ctx

class UVarInfo(using Context)(val name: String, val typ: Expr) {
  ctx.trackUVarInfo(this)
  private var myInstance: Expr | Null = null
  def instantiated: Boolean = myInstance ne null
  def instantiate(x: Expr): this.type =
    assert(!instantiated)
    myInstance = x
    this
  def instance: Expr = myInstance.nn
  def instanceOpt: Option[Expr] =
    if instantiated then Some(myInstance.nn) else None

  override def toString(): String =
    if instantiated then s"[$instance]"
    else s"VarInfo($name, $typ)"
}

