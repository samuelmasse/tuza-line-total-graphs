$ErrorActionPreference = 'Stop'
$taskRoot = Split-Path -Parent $PSScriptRoot
Push-Location $taskRoot
try {
    & lake build
    if ($LASTEXITCODE -ne 0) { throw 'The implemented Lean library did not build.' }
    & lake env lean scripts/CheckReady.lean
    if ($LASTEXITCODE -ne 0) {
        throw 'Not ready for Palomar: missing headline proofs or unapproved axioms.'
    }
    Write-Output 'Headline declarations and local axiom audit passed. Comparator and NanoDa replay are still required.'
}
finally {
    Pop-Location
}
