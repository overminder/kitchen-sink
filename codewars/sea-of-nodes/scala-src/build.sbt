scalaVersion := "2.11.8"

// Turn on -Werror
scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature", "-Xfatal-warnings")

mainClass := Some("com.github.overmind.seaofnodes.Main")
