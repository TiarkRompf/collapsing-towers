scalaVersion := "2.12.3"

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.6"

resolvers += "Sonatype OSS Snapshots" at
  "https://oss.sonatype.org/content/repositories/snapshots"

libraryDependencies += "com.storm-enroute" %% "scalameter" % "0.19"

testFrameworks += new TestFramework(
    "org.scalameter.ScalaMeterFramework")

logBuffered := false

parallelExecution in Test := false
