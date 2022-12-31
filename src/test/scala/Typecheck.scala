import driver.Driver._

import java.nio.file.{FileSystems, Files}
import scala.collection.JavaConverters._

class TypecheckSuite extends munit.FunSuite {
  val dir = FileSystems.getDefault.getPath("tests/")

  for path <- Files.list(dir).iterator().asScala do
    test(path.toString) {
      assertEquals(checkFile(path.toString), None)
    }
}
