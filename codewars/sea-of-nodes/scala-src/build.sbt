scalaVersion := "2.11.8"

// resolvers += Resolver.sonatypeRepo("releases")

// Turn on -Werror
scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature", "-Xfatal-warnings")

libraryDependencies ++= Seq(
  // Parser combinator.
  "com.lihaoyi" %% "fastparse" % "0.3.7",

  // Macro API.
  "org.scala-lang" % "scala-reflect" % "2.11.8"
)

mainClass := Some("com.github.overmind.seaofnodes.Main")

