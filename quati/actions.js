/*
 * Giselle Reis
 * 08.2013
 */

// Because of Firefox's incompatibility with innerText
function setText(node, text) {
  if(node.innerText !== undefined) {
    node.innerText = text;
  }
  else {
    node.textContent = text;
  }
}

/*
 * actions:
 * - bipoles -> get the bipoles for the system
 *   params: system name
 * - permute -> check the permutation of rules
 *   params: system name, rule 1, rule 2
 *
 */

function genBipoles(sysName) {
  
  document.getElementById('result').style.display = 'none'
  
  var xmlhttp = false;
  if (window.XMLHttpRequest) {
    // code for IE7+, Firefox, Chrome, Opera, Safari
    xmlhttp=new XMLHttpRequest();
  }
  else {
  // code for IE6, IE5
    xmlhttp=new ActiveXObject("Microsoft.XMLHTTP");
  }

  // When the answer is received:
  xmlhttp.onreadystatechange = function () {
    if(xmlhttp.readyState == 4 && xmlhttp.status == 200) {
      var response = xmlhttp.responseText
      document.getElementById('bipoles').style.display = 'block'
      setText(document.getElementById('bipolesTex'), "The bipoles for " + sysName + " are:\n" + "\\[" + response + "\\]")
      var math = document.getElementById("bipolesTex");
      MathJax.Hub.Queue(["Typeset",MathJax.Hub,math]);
    }
  }
 
  var query = "?system="+sysName
  xmlhttp.open("GET", "bipoles.py"+query, true)
  xmlhttp.send()

}

function checkPermutation() {
  
  var system = document.getElementById('select').value
  var r1 = document.getElementById('r1').value
  var r2 = document.getElementById('r2').value

  if(r1 == '' || r2 == '') {
    alert("You must select the rules by typing their numbers in the boxes.")
    return
  }

  var xmlhttp = false;
  if (window.XMLHttpRequest) {
    // code for IE7+, Firefox, Chrome, Opera, Safari
    xmlhttp=new XMLHttpRequest();
  }
  else {
  // code for IE6, IE5
    xmlhttp=new ActiveXObject("Microsoft.XMLHTTP");
  }

  // When the answer is received:
  xmlhttp.onreadystatechange = function () {
    if(xmlhttp.readyState == 4 && xmlhttp.status == 200) {
      var response = xmlhttp.responseText
      document.getElementById('result').style.display = 'block'
      setText(document.getElementById('permutationsTex'), "The permutation of rules " + r1 + " and " + r2 + " of the system " + system + " are:\n" + "\\[" + response + "\\]")
      var math = document.getElementById("permutationsTex");
      MathJax.Hub.Queue(["Typeset",MathJax.Hub,math]);
    }
  }

  var query = "?system=" + system + "&r1=" + r1 + "&r2=" + r2
  xmlhttp.open("GET", "bipoles.py"+query, true)
  xmlhttp.send()

}
