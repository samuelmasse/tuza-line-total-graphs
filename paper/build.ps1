$ErrorActionPreference = 'Stop'
$taskRoot = Split-Path -Parent $PSScriptRoot
$taskBuild = Join-Path $taskRoot 'tmp/paper-build'
New-Item -ItemType Directory -Path $taskBuild -Force | Out-Null
Copy-Item -LiteralPath (Join-Path $PSScriptRoot 'main.tex'), (Join-Path $PSScriptRoot 'references.bib') -Destination $taskBuild
Push-Location $taskBuild
try {
    & pdflatex --disable-installer -interaction=nonstopmode -halt-on-error main.tex
    if ($LASTEXITCODE -ne 0) { throw 'First LaTeX pass failed.' }
    & bibtex main
    if ($LASTEXITCODE -ne 0) { throw 'BibTeX failed.' }
    1..2 | ForEach-Object {
        & pdflatex --disable-installer -interaction=nonstopmode -halt-on-error main.tex
        if ($LASTEXITCODE -ne 0) { throw 'LaTeX pass failed.' }
    }
    Copy-Item -LiteralPath (Join-Path $taskBuild 'main.pdf') -Destination (Join-Path $PSScriptRoot 'tuza-line-total-graphs.pdf')
}
finally {
    Pop-Location
}
