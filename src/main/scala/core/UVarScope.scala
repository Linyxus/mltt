package core

class UVarScope(parent: UVarScope | Null, trackedUVars: List[UVarInfo]) {
  def track(info: UVarInfo): UVarScope = UVarScope(parent, info :: trackedUVars)
  def checkUninstantiated: List[UVarInfo] =
    trackedUVars.filterNot(_.instantiated)
}

