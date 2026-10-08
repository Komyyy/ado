import VersoBlog
import AdoPage

open Verso Genre Blog Site Syntax

def blog : Site := site AdoPage.FrontPage /
  "posts" AdoPage.Posts with
    AdoPage.Posts.FirstPage
    AdoPage.Posts.SubobjectHell
    AdoPage.Posts.SubobjectHellEn

def main := blogMain .default blog
