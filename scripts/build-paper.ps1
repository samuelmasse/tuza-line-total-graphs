$ErrorActionPreference = 'Stop'
$repoRoot = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$buildDir = Join-Path $repoRoot 'tmp/pdfs/paper-build'
$paperDir = Join-Path $repoRoot 'paper'
New-Item -ItemType Directory -Force $buildDir | Out-Null
Copy-Item -LiteralPath (Join-Path $paperDir 'main.tex'), (Join-Path $paperDir 'references.bib') -Destination $buildDir

Push-Location $buildDir
try {
    & pdflatex -disable-installer -interaction=nonstopmode -halt-on-error main.tex
    if ($LASTEXITCODE -ne 0) { throw 'First LaTeX pass failed.' }
    & bibtex main
    if ($LASTEXITCODE -ne 0) { throw 'BibTeX failed.' }
    foreach ($pass in 1..2) {
        & pdflatex -disable-installer -interaction=nonstopmode -halt-on-error main.tex
        if ($LASTEXITCODE -ne 0) { throw "LaTeX pass $pass failed." }
    }
    Copy-Item -LiteralPath (Join-Path $buildDir 'main.pdf') -Destination (Join-Path $paperDir 'tuza-line-total-graphs.pdf')
} finally {
    Pop-Location
}
Write-Output (Join-Path $paperDir 'tuza-line-total-graphs.pdf')
