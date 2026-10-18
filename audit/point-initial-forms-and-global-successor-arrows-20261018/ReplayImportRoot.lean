import LeanChecker

-- Use the installed LeanChecker implementation for this exact import-only root.
-- The CLI's Hironaka prefix would select every module, so invoke its same
-- replayFromImports entry point directly for Hironaka alone.
#eval do
  Lean.initSearchPath (← Lean.findSysroot)
  replayFromImports `Hironaka
  IO.println "REPLAYED_EXACT_IMPORT_ROOT Hironaka"
