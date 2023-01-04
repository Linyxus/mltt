package core

class UVarScope(val parent: UVarScope | Null) {
  private var trackedUVars: List[UVarInfo] = Nil

  def track(info: UVarInfo): Unit =
    trackedUVars = info :: trackedUVars
  def checkUninstantiated: List[UVarInfo] =
    trackedUVars.filterNot(_.instantiated)

  override def toString: String = s"UVarScope($trackedUVars)"
}

