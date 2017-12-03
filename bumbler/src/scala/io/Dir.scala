package io

import java.io.File

trait DirTrait {


    def list(path: String = "."): Array[java.io.File] = {
        (new java.io.File(path)).listFiles
    }

    def listFiles(path: String = "."): Array[java.io.File] = {
        for {
            file <- list(path)
            if file.isFile
        }
        yield file
    }

    def listFilesWithExt(ext: String, path: String = "."): Array[java.io.File] = {
        for {
            file <- list(path)
            if file.isFile
            if file.getName.endsWith(ext)
        }
        yield file
    }


    private def filesMatching(
        path: String,
        matcher: (String) => Boolean,
        onlyFile: Boolean = false
    ): Array[File] = {
        for (file <- list(path);
             if !onlyFile || file.isFile;
             if matcher(file.getName))
            yield file
    }

    def filesEnding(query: String, path: String = ".", onlyFile: Boolean = false) =
        filesMatching(path, _.endsWith(query), onlyFile)

    def filesContaining(query: String, path: String = ".", onlyFile: Boolean = false) =
        filesMatching(path, _.contains(query), onlyFile)

    def filesRegex(query: String, path: String = ".", onlyFile: Boolean = false) =
        filesMatching(path, _.matches(query), onlyFile)


    def fileLines(file: java.io.File): List[String] = 
        scala.io.Source.fromFile(file).getLines.toList

    def grep(
        pattern: String,
        path: String = ".",
        fileName: String = ".*"
    ): Array[String] = {
        for {
            file <- listFiles(path)
            if file.getName.matches(fileName)
            line <- fileLines(file)
            trimmed = line.trim
            if trimmed.matches(pattern)
        }
        yield trimmed
    }

}

object Dir extends DirTrait
