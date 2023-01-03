import driver.Driver._

@main def run(): Unit = {
  val source = """
def test: Type = ???
"""

  println(check(source))
}
