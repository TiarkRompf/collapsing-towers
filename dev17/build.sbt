resolvers += "Sonatype OSS Snapshots" at
  "https://oss.sonatype.org/content/repositories/snapshots"

libraryDependencies += "com.storm-enroute" %% "scalameter" % "0.8.2"

testFrameworks += new TestFramework(
    "org.scalameter.ScalaMeterFramework")
  
logBuffered := false

parallelExecution in Test := false
