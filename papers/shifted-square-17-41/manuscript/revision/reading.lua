function Div(el)
  if FORMAT == "latex" then
    el.identifier = el.identifier:gsub("^ref%-", "reference-")
    for i = #el.classes, 1, -1 do
      if el.classes[i] == "reference" then table.remove(el.classes, i) end
    end
  end
  return el
end
