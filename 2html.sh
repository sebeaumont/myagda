find src -name '[A-Z]*.org' | xargs -n1 agda --html --html-highlight=code
echo "now don't forget to publish the project from html"
