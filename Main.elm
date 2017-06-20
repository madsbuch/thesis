module Main exposing (..)

import Html exposing (..)
import Html.Attributes exposing (..)
import Markdown as Markdown
import Material
import Material.Scheme
import Material.Layout as Layout
import Material.Grid as G
import Material.Card as Card
import Material.Button as Button 
import Material.Options as Options exposing (cs, css)
import Material.Color as Color
import Material.Elevation as Elevation

-- MODEL
type alias Model = {
     mdl : Material.Model
    ,raised : Int
}


init : ( Model, Cmd a )
init = ({
         mdl = Material.model
        ,raised = -1
    }, Cmd.none)

-- MSG

type alias Mdl =
    Material.Model

type Msg = 
      NoOp
    | Raise Int
    | Mdl (Material.Msg Msg)

-- UPDATE

update : Msg -> Model -> ( Model, Cmd Msg )
update msg model =
    case msg of
        NoOp                    -> model |> noCmd
        Raise k                 -> {model | raised = k} |> noCmd
        Mdl msg_                -> Material.update Mdl msg_ model

noCmd model = (model, Cmd.none)

-- LAYOUT

layout model =

    Layout.render Mdl model.mdl [ Layout.fixedHeader ]
      { header = header
      , drawer = []
      , tabs = ([], [])
      , main = (top model)
      } |> Material.Scheme.top

header : List (Html Msg)
header = 
          [node "meta" [ name "viewport", content "width=device-width, initial-scale=1, maximum-scale=1, user-scalable=no" ] []] ++
          [ Layout.row
              [ css "transition" "height 333ms ease-in-out 0s"]
              [ Layout.title [] [ text "Formalizing Differential Privacy" ]
              , Layout.spacer
              , Layout.navigation []
                  [ Layout.link
                      [ Layout.href "http://madsbuch.com/thesis/presentation"]
                      [ span [] [text "Defense Presentation"] ]
                  , Layout.link
                      [ Layout.href "https://github.com/madsbuch/thesis"]
                      [ span [] [text "GitHub"] ]
                  , Layout.link
                      [ Layout.href "https://github.com/madsbuch/thesis/archive/gh-pages.zip" ]
                      [ text "Download Zip" ]
                  ]
              ]
          ]

top : Model -> List (Html Msg)
top model =
  [  G.grid []
           [ card model 11 "Thesis" "The pdf"
                "http://github.com/madsbuch/thesis/blob/gh-pages/thesis.pdf"
                "Download"
                "https://s-media-cache-ak0.pinimg.com/originals/4c/75/b9/4c75b9b14f9bd94abee3fd9054892fd4.jpg"
           , card model 10 "Virtual Machine" "Preloaded with resources"
                "https://www.dropbox.com/s/hdiozbruyx1zb16/mads-buch-master-thesis-vitual-machine.tar.gz"
                "Download"
                "https://tr1.cbsistatic.com/hub/i/r/2016/12/06/f3f2bd25-6c00-4f85-bfd7-51d3da18934d/resize/770x/1c6e838bd486d47d96d37788780e8779/vbhero.jpg"
           , G.cell [G.size G.Desktop 6, G.size G.Tablet 8, G.size G.Phone 6]
              [ h3 [] [text "Abstract"]
              , p  [] [abstract]]]]

  ++ [G.grid []
           [ card model 1 "Case Study 1" "Randomized Response"
                "http://github.com/madsbuch/thesis/blob/gh-pages/case-studies/1-randomized-response.ec"
                "See it on GitHub"
                "https://www.random.org/analysis/randbitmap-rdo-section.png"
           , card model 2 "Case Study 2" "Laplace"
                "http://github.com/madsbuch/thesis/blob/gh-pages/case-studies/2-lap.ec"
                "See it on GitHub"
                "http://www.sil.si.edu/DigitalCollections/hst/scientific-identity/fullsize/SIL14-L002-01a.jpg"
           , card model 3 "Case Study 3" "Sums over Stream"
                "http://github.com/madsbuch/thesis/blob/gh-pages/case-studies/3-sums.ec"
                "See it on GitHub"
                "https://www.thesun.co.uk/wp-content/uploads/2016/09/nintchdbpict000266409417.jpg"
           , card model 4 "Case Study 4" "Sparse Vector Technique"
                "http://github.com/madsbuch/thesis/blob/gh-pages/case-studies/4-svt.ec"
                "See it on GitHub"
                "http://www.freysmiles.com/images/uploads/general/deserted_island.jpeg"
           ]]
  ++ [G.grid [] [
           G.cell [G.size G.Desktop 12, G.size G.Tablet 8, G.size G.Phone 6]
              [ h3 [] [text "Errata"]
              , p  [] [errata]]
           ]]

abstract = Markdown.toHtml [] """
Differential privacy's primary goal is to release
data in a privacy-preserving manner. Differential privacy is the name of
a framework that quantifies privacy-loss from one database to another.
For a protocol to be differentially private, we prove an upper bound on
the privacy loss between two adjacent databases.
Databases are adjacent if they
satisfy an adjacency relation. The technique promises
that performing a single alternation to a database poses no
statistical difference in the output of a differentially private protocol.
This is promising for privacy, but implementing such techniques can be hard and
raises several subtleties. To compensate we employ formal
techniques to ensures that an implementation is correct.
"""

errata = Markdown.toHtml [] """
* __June 18th 2017__ Corrected definition of pRHL and apRHL judgments.
"""

card model k title descr btnUrl btnT imgUrl = G.cell [G.size G.Desktop 3, G.size G.Tablet 4, G.size G.Phone 6] [Card.view
  [  css "width" "100%"
    --,Color.background (Color.color Color.LightBlue Color.S400)
    -- Elevation
    , if model.raised == k then Elevation.e8 else Elevation.e2
    , Elevation.transition 250
    , Options.onMouseEnter (Raise k)
    , Options.onMouseLeave (Raise -1)
    ]
  [ Card.title
      [ css "background" ("url('" ++ imgUrl ++ "') center / cover")
      , css "height" "256px"
      , css "padding" "0" -- Clear default padding to encompass scrim
      ]
      [ Card.head
          [ (Color.text Color.white )
          , Options.scrim 0.75
          , css "padding" "16px" -- Restore default padding inside scrim
          , css "width" "100%"
          ]
          [ text title ]
      ]
  , Card.text []
      [ text descr ]
  , Card.actions
      [ Card.border ]
      [ Button.render Mdl [1,0] model.mdl
          [ Button.ripple
          , Button.accent
          ,Button.link btnUrl ]
          [ text btnT ]
      ]
  ]]

-- MAIN

main : Program Never Model Msg
main =
    program
        { init = init
        , view = layout
        , update = update
        , subscriptions = \n -> Sub.none
        }
