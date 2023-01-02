import driver.Driver._

@main def run(): Unit = {
  val source = """
def id(A: Type): (x: A) -> A = x => x
"""
  println(check(source))
}
