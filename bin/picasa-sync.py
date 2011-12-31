#!/usr/bin/env python

# From https://cychong.wordpress.com/2011/03/24/download-original-pictures-from-the-picasaweb/

import gdata.photos.service
import gdata.media
import gdata.geo
import urllib
import os
import sys
import re

URL_TO_GET_PHOTOS 	= '/data/feed/api/user/default/albumid/%s?kind=photo'
URL_TO_GET_TAGS 	= '/data/feed/api/user/default/albumid/%s/photoid/%s?kind=tag' 
URL_TO_GET_COMMENTS	= '/data/feed/api/user/default/albumid/%s/photoid/%s?kind=comment'

USER_ID			= os.environ['GOOGLE_USER_ID']
USER_PASSWORD		= os.environ['GOOGLE_USER_PASSWORD']

def sanitize ( path ) :
        return re.sub("/", "-", path)

def download_file( url, dir_name ):
	"Download the data at URL to the current directory"
	basename = url[url.rindex('/') + 1:] # figure out a good name for the downloaded file.
	url = url.replace(basename, "d/"+basename)

        new_file = dir_name+"/"+sanitize(basename)

        get = False

        if not os.path.exists( new_file ) :
                get = True
        else :
                # Turn this to True to enable file size checking
                if False :
                        site = urllib.urlopen(url)
                        meta = site.info()
                        web_len = int(meta.getheaders("Content-Length")[0])
                        f = open(new_file, "rb")
                        here_len = len(f.read())
                        f.close()
                        if web_len != here_len :
                                print '\tFile size mismatch: %d vs %d\n' % (web_len, here_len) 
                                get = True

        if get : 
                urllib.urlretrieve(url, new_file)

def connect_to_picasa( name, password ):
	gd_client = gdata.photos.service.PhotosService()
	gd_client.email = USER_ID
	gd_client.password = USER_PASSWORD
	gd_client.source = 'api-sample-google-com'
	gd_client.ProgrammaticLogin()

	return gd_client

def get_album_list( gd_client ):
	return gd_client.GetUserFeed()

def print_photo_list( albums ):
	for album in albums.entry:
		downloaded_photos = 0
		print 'Album: %s (%s)' % (album.title.text, album.numphotos.text)

                album_dir = sanitize(album.title.text)
		if not os.path.exists(album_dir) :
			os.mkdir(album_dir)

		photos = gd_client.GetFeed(URL_TO_GET_PHOTOS % (album.gphoto_id.text))

		for photo in photos.entry:
			download_file( photo.content.src, album_dir )
			downloaded_photos += 1

			sys.stdout.write("\t%d/%s  %.1f %%\r" %(downloaded_photos, album.numphotos.text, 100.0*downloaded_photos/eval(album.numphotos.text)))
			sys.stdout.flush()

		print ""
		

if __name__ == '__main__':
	gd_client = connect_to_picasa( USER_ID, USER_PASSWORD )
	albums = get_album_list( gd_client )
	print_photo_list( albums )
	

