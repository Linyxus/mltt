package core

import ast.TypedExprs._
import ast.SrcPos
import Context.ctx

case class CreationSite(site: SrcPos, reason: String)

class UVarInfo(using Context)(val name: String, val typ: Expr, val creator: CreationSite) {
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
    else s"UVarInfo($name, $typ)"
}

