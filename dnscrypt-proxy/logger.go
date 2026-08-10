package main

import (
	"io"
	"os"

	"github.com/jedisct1/dlog"
	"gopkg.in/natefinch/lumberjack.v2"
)

func Logger(logMaxSize int, logMaxAge int, logMaxBackups int, fileName string) io.Writer {
	if fileName == "/dev/stdout" {
		return os.Stdout
	}
	if st, _ := os.Stat(fileName); st != nil && !st.Mode().IsRegular() {
		if st.Mode().IsDir() {
			dlog.Fatalf("[%v] is a directory", fileName)
		}
		// Special files (devices, pipes) are opened directly
		// Note: The caller is responsible for closing the returned file descriptor
		// This is handled by the plugin cleanup during proxy shutdown
		fp, err := os.OpenFile(fileName, os.O_WRONLY|os.O_APPEND|os.O_CREATE, 0o644)
		if err != nil {
			dlog.Fatalf("Unable to access [%v]: [%v]", fileName, err)
		}
		return fp
	}
	// Create the file before lumberjack does: it only opens it on the first write, where errors get discarded.
	// This also keeps the mode at 0644 instead of lumberjack's 0600.
	// Logs are meant to stay readable by regular users; restricting access is the parent directory's job.
	if fp, err := os.OpenFile(fileName, os.O_WRONLY|os.O_APPEND|os.O_CREATE, 0o644); err == nil {
		fp.Close()
	} else {
		dlog.Errorf("Unable to create [%v]: [%v]", fileName, err)
	}
	logger := &lumberjack.Logger{
		LocalTime:  true,
		MaxSize:    logMaxSize,
		MaxAge:     logMaxAge,
		MaxBackups: logMaxBackups,
		Filename:   fileName,
		Compress:   true,
	}

	return logger
}
